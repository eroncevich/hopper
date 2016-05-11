package edu.colorado.hopper.client.android

import com.ibm.wala.analysis.pointers.HeapGraph
import com.ibm.wala.ipa.callgraph.{CGNode, CallGraph}
import com.ibm.wala.ipa.callgraph.propagation.{HeapModel, InstanceKey}
import com.ibm.wala.ipa.cha.IClassHierarchy
import com.ibm.wala.ssa.SSAPutInstruction
import com.ibm.wala.util.graph.traverse.BFSIterator
import com.ibm.wala.util.intset.OrdinalSet
import edu.colorado.droidel.driver.AndroidAppTransformer
import edu.colorado.hopper.state._
import edu.colorado.hopper.util.PtUtil
import edu.colorado.walautil.{GraphUtil, IRUtil}

import scala.collection.JavaConversions._

/**
  * Created by evan on 5/11/16.
  */
class AndroidSlicingRelevanceRelation(appTransformer : AndroidAppTransformer, cg : CallGraph, hg : HeapGraph[InstanceKey],
                               hm : HeapModel, cha : IClassHierarchy,
                               cgTransitiveClosure : java.util.Map[CGNode,OrdinalSet[CGNode]] = null)
  extends AndroidRelevanceRelation(appTransformer, cg, hg, hm, cha, cgTransitiveClosure) {

  /** given an application-space CGNode n, compute the node(s) invoked by the framework that may call this node.
    * to be more concrete, if the app is onCreate() { foo() } onDestroy() { foo() } and n is foo, then this
    * method will return {onCreate, onDestroy} */
  override def getLibraryAppFrontierNodesFor(n : CGNode) : Set[CGNode] = {
    // library nodes are already on the wrong side of the library/app frontier, can't do anything
    if (isFrameworkOrStubNode(n)) Set(n) //Modify this to check to return to application
    else {
      val iter = new BFSIterator[CGNode](cg, n) {
        override def getConnected(n: CGNode): java.util.Iterator[_ <: CGNode] = {
          cg.getPredNodes(n).filter(n => !isFrameworkOrStubNode(n))
        }
      }

      def hasNonAppPred(n: CGNode): Boolean = cg.getPredNodes(n).exists(n => isFrameworkOrStubNode(n))

      val initFrontierNodes = if (hasNonAppPred(n)) Set(n) else Set.empty[CGNode]
      GraphUtil.bfsIterFold(iter, initFrontierNodes, ((s: Set[CGNode], n: CGNode) =>
        if (hasNonAppPred(n)) s + n
        else s
        ))
    }
  }


  /** return Some(paths) if we should jump, None if we should not jump */
  override def getPiecewisePaths(p: Path, jmpNum: Int): Option[List[Path]] = {
    if (DEBUG) println("Computing relevance graph")
    if (p.qry.heapConstraints.isEmpty) None // no heap constraints, pointless to jump
    else {
      val qry = p.qry
      val modMap = super.getNodeModifierMap(qry, ignoreLocalConstraints = true)
      println("MM"+modMap)
      for(m<-modMap){for(instr<-m._2){ instr match{
        case i:SSAPutInstruction => p.qry.addSeed(Variable(i.getUse(1),p.node ))
        case _ => ???
      }

      }}
      if (DEBUG) println(s"Before control-feas filtering, ${modMap.keys} are relevant")
      val (nodesToJumpToMustAlias, nodesToJumpToMustNotAlias) = controlFeasibilityFilter(modMap, qry.node)

      p.clearCallStack()

      def addReceiverConstraint(qry: Qry, jmpNode: CGNode, mustAlias: Boolean): Unit =
        if (!jmpNode.getMethod.isStatic) {
          val thisLPK = Var.makeLPK(IRUtil.thisVar, jmpNode, hm)
          val thisPT = PtUtil.getPt(thisLPK, hg)
          qry.heapConstraints.find(e => e match {
            case ObjPtEdge(src@ObjVar(srcRgn), _, _) if !srcRgn.intersect(thisPT).isEmpty =>
              val receiverVar =
                if (mustAlias) src // must-alias, use src
                else {
                  // must-not-alias, create fresh var
                  val freshReceiverObjVar = ObjVar(thisPT)
                  Var.markCantAlias(freshReceiverObjVar, src)
                  freshReceiverObjVar
                }
              qry.addLocalConstraint(PtEdge.make(Var.makeLocalVar(IRUtil.thisVar, jmpNode, hm), receiverVar))
              true
            case _ => false
          })
        }

      def setUpJumpPaths(nodesToJumpTo: Set[CGNode], mustAlias: Boolean, paths: List[Path] = Nil) =
        nodesToJumpTo.foldLeft(paths)((paths, jmpNode) => {
          val copy = p.deepCopy
          val jmpBlk = jmpNode.getIR.getExitBlock
          val qry = copy.qry
          Path.setupBlockAndCallStack(copy, jmpNode, jmpBlk, -1, jmpNum)
          // transfer the this constraint from the current method to the jump method
          addReceiverConstraint(qry, jmpNode, mustAlias)
          copy :: paths
        })

      val mustAliasCases = setUpJumpPaths(nodesToJumpToMustAlias, mustAlias = true)
      val jumpPaths = setUpJumpPaths(nodesToJumpToMustNotAlias, mustAlias = false, mustAliasCases)
      //for(p<-jumpPaths){println(p.qry.node.getIR)}
      //for(p<-jumpPaths){p.qry.getSlice(modMap(p.qry.node))}
      //val jumpDepPaths = jumpPaths.map{p=>Path()}
      Some(jumpPaths)
    }
  }

}