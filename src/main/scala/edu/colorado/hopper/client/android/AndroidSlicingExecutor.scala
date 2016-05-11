package edu.colorado.hopper.client.android

import com.ibm.wala.analysis.pointers.HeapGraph
import com.ibm.wala.ipa.callgraph.CGNode
import com.ibm.wala.ipa.callgraph.propagation.{InstanceKey, HeapModel}
import com.ibm.wala.ssa._
import com.ibm.wala.util.graph.traverse.BFSIterator
import edu.colorado.droidel.constants.DroidelConstants
import edu.colorado.hopper.executor.TransferFunctions
import edu.colorado.hopper.jumping.{DefaultJumpingSymbolicExecutor, RelevanceRelation}
import edu.colorado.hopper.state.Path
import edu.colorado.hopper.state._
import edu.colorado.hopper.util.PtUtil
import edu.colorado.thresher.core.Options
import edu.colorado.walautil.{GraphUtil, CGNodeUtil, ClassUtil}
import scala.collection.JavaConversions._


import scala.io.Source


/**
  * Created by evan on 5/9/16.
  */
class AndroidSlicingExecutor(tf: TransferFunctions, rr: RelevanceRelation, hm: HeapModel, hg: HeapGraph[InstanceKey])
  extends AndroidJumpingSymbolicExecutor(tf, rr) {
  val MIN_DEBUG = Options.DEBUG

  override def returnFromCall(p: Path): Iterable[Path] = {
    println("retrnFromCall")
    if (p.qry.node.getMethod.getSelector.getName.toString == "onCreate") {
      println("Reached the beginning of the Activity, purposely returning")
      throw WitnessFoundException
    }
    if (p.qry.node.getMethod.getSelector.getName.toString == "onClick") {
      val qry = p.qry
      val caller = getCallers(cg, qry.node).head
      println(caller)
      val instrs = caller.getIR.getInstructions.filter { i => i match {
        case ii: SSAInvokeInstruction => cg.getPossibleTargets(caller, ii.getCallSite()).contains(qry.node)
        case _ => false
      }
      }
      val heapInstrs = caller.getIR.getInstructions.find { i => i match {
        case ii: SSAGetInstruction => i.iindex == 17
        case _ => false
      }
      }
      val heapInstr = heapInstrs match {
        case Some(i: SSAGetInstruction) => i
        case _ => throw new ClassCastException
      }

      val instr = instrs.head match {
        case i: SSAInvokeInstruction => i
        case _ => throw new ClassCastException
      }
      println(instr)
      val invokeUse = instr.getDef
      val receiver = Var.makeLPK(1, qry.node, hm)
      val iFld = cha.resolveField(heapInstr.getDeclaredField)
      val instKeys = PtUtil.getPt(Var.makeLPK(heapInstr.getRef, caller, hm), hg)

      //PtEdge.make(null:HeapVar,iFld,ObjVar(PtUtil.getPt(receiver, walaRes.hg)))
      val hConstraint = PtEdge.make(ObjVar(instKeys), iFld, ObjVar(PtUtil.getPt(receiver, hg)))
      qry.addHeapConstraint(hConstraint)
      return doJump(p)

    }else{
      //return super.returnFromCallNoJump(p)
      return returnNoJump(p)
    }
  }
  def isFrameworkOrStubNode(n : CGNode) : Boolean =
    ClassUtil.isLibrary(n) || {
      val methodName = n.getMethod.getDeclaringClass.getName.toString
      methodName.startsWith(s"L${DroidelConstants.STUB_DIR}") ||
        methodName.startsWith(s"L${DroidelConstants.HARNESS_DIR}") ||
        methodName.startsWith(s"L${DroidelConstants.PREWRITTEN_STUB_DIR}")
    }

  val frameworkSet:collection.immutable.Set[String] = {
    Source.fromFile("frameworkO").getLines.foldLeft(collection.immutable.Set[String]()) {(a,l) =>a + l}
  }
  val isFwkRelevant : SSAInvokeInstruction => Boolean = instr =>{
    val funStr = instr.getDeclaredTarget.getDeclaringClass.getName.toString
    println(funStr)

    frameworkSet.contains(funStr)
  }

  override def executeInstr(paths : List[Path], instr : SSAInstruction, blk : ISSABasicBlock, node : CGNode, cfg : SSACFG,
                   isLoopBlk : Boolean, callStackSize : Int) : List[Path] = instr match {
    case instr: SSAInvokeInstruction =>
      println("Is Relevant: " + isFwkRelevant(instr))
      if (isFwkRelevant(instr)) {
        val caller = Variable(instr.getReceiver, node)
        val args = {
          1 to instr.getNumberOfParameters - 1
        }.map { ii => Variable(instr.getUse(ii), node) }

        val caller_loc = node.getMethod.getSourcePosition(instr.iindex)
        val callee = FrameworkFun(instr.getDeclaredTarget.toString, caller_loc) // (callee * caller_location)

        // add dep edge from current method context to callee
        for (a <- args) {
          for (p <- paths) {
            p.qry.addDepEdge(caller, a, callee)
          }
        }
        /*for(p <- paths){
          val callNode = cg.getNodes(instr.getDeclaredTarget).head
          for(ii <- {0 to instr.getNumberOfParameters-1}){
            p.qry.addDepEdge(Variable(instr.getUse(ii),node),Variable(ii+1,callNode),FrameworkFun("argument",null))
          }
        }*/
      }
      val (enterPaths, skipPaths) = enterCallee(paths, instr)
      if (!enterPaths.isEmpty) {
        if (DEBUG)
          println(s"Entering call ${instr.getDeclaredTarget().getName()} from ${node.getMethod().getName()} full names ${ClassUtil.pretty(instr.getDeclaredTarget())} from ${ClassUtil.pretty(node)}")
        val paths = executeBackwardWhile(enterPaths, p => p.callStackSize != callStackSize, skipPaths)
        if (DEBUG)
          println(s"Returning from call to ${ClassUtil.pretty(instr.getDeclaredTarget())} back to ${ClassUtil.pretty(node)}; have ${paths.size} paths.")
        paths
      } else {
        if (DEBUG)
          if (!skipPaths.isEmpty) println(s"decided to skip call $instr; have ${skipPaths.size}")
          else println(s"Refuted by call to $instr")
        skipPaths
      }
    case _ => super.executeInstr(paths, instr, blk, node, cfg, isLoopBlk, callStackSize)
  }

  def checkPathReturnsToApp(caller: CGNode): Boolean = {
    val iter = new BFSIterator[CGNode](cg, caller) {
      override def getConnected(n: CGNode): java.util.Iterator[_ <: CGNode] = {
        //println("con"+ n)
        //println("Step Top")
        val possiblePreds = cg.getPredNodes(n).filter(n => isFrameworkOrStubNode(n) && {
          connectedHelper(n,3).isEmpty
        })
        val preds = cg.getPredNodes(n).filter(n =>  !isFrameworkOrStubNode(n))
        preds++possiblePreds
      }
      def connectedHelper(n: CGNode, steps:Int):Set[CGNode] = {
        if(steps==0) return Set()
        //println("step "+steps)
        val possiblePreds = cg.getPredNodes(n).filter(n => isFrameworkOrStubNode(n) && {
          connectedHelper(n,steps-1).isEmpty
        })
        //val possPreds = pred.foldLeft(Set():Set[CGNode]){(a,n) => a ++ (connectedHelper(n,steps-1))}
        val preds = cg.getPredNodes(n).filter(n => !isFrameworkOrStubNode(n))
        preds.toSet ++ possiblePreds.toSet
      }
    }

    //val initNodes = if (!isFrameworkOrStubNode(caller)) Set(caller) else Set.empty[CGNode]

    val validNodes = GraphUtil.bfsIterFold(iter, Set.empty[CGNode], ((s: Set[CGNode], n: CGNode) =>
      s+n
      )).filter(n => (n!=caller) || !isFrameworkOrStubNode(n))
    println("care: "+ validNodes)

    true
  }

  def returnNoJump(p : Path) : Iterable[Path] = {
    val callee = p.callStack.top.node // get rid of current stack frame

    if (p.callStackSize == 1) {
      // no calling context; have to consider all callers in call graph
      if (DEBUG) println("at function boundary of node " + ClassUtil.pretty(callee))

      if (callee == CGNodeUtil.getFakeWorldClinitNode(cg).get) sys.error("should be handled elsewhere")
      // TODO: execute other entrypoints also? answer depends on harness
      else if (callee == cg.getFakeRootNode() || callee.getMethod().isClinit()) List(p)
      else { // else, return to caller with no context
      val callers = getCallers(cg, callee)
        if (MIN_DEBUG) println(s"Context-free return; branching from ${ClassUtil.pretty(callee)} to ${callers.size} callers.")
        val newPaths = callers.foldLeft (List.empty[Path]) ((lst, caller) => {
          val callerPath = p.deepCopy

          val validPath = checkPathReturnsToApp(caller) // check that the CG can somehow get back to Application Code
          if(!validPath){
            lst
          }else{
            // create a path for each caller and call site of the current method
            if (MIN_DEBUG) println("caller: " + ClassUtil.pretty(caller))
            if (callerInvMap.pathEntailsInv((caller, callee), callerPath)) {
              if (Options.PRINT_REFS) println("Refuted by caller summary.")
              lst // refuted by summary
            } else {
              //if (UnstructuredSymbolicExecutor.PRINT_IR) println(caller.getIR())
              val recursive = caller.equals(callee)
              val callerIR = caller.getIR()
              val callerCFG = callerIR.getControlFlowGraph()

              // get all call instructions in caller that might call callee
              callerIR.getInstructions().zipWithIndex.collect({
                case (i : SSAInvokeInstruction, index) if cg.getPossibleTargets(caller, i.getCallSite()).contains(callee) => (i, index)
              })
                .foldLeft (lst) ((lst, pair) => {
                  println("PC" +caller)
                  val (invoke, index) = pair
                  val sitePath = callerPath.deepCopy
                  if (recursive) {
                    // TODO: handle mutual recursion here? need to track repeated sequences of bw visited calls
                    if (DEBUG) println("handled recursive call while forking to all callers--dropping constraints")
                    sitePath.dropConstraintsProduceableInCall(invoke, caller, callee, tf)
                  }
                  //val callBlk = callerCFG.exit()
                  val callBlk = callerCFG.getBlockForInstruction(index)
                  println(callBlk.getLastInstruction)
                  // call is always the last instruction in a block. set to line *before* the call
                  val callLine = callBlk.asInstanceOf[SSACFG#BasicBlock].getAllInstructions().size - 2
                  assert(callBlk.getLastInstruction == invoke,
                    s"Expected call to be last instruction in $callBlk, but got ${callBlk.getLastInstruction}. IR $callerIR")
                  if (sitePath.returnFromCall(caller, callee, callBlk, callLine, invoke, tf)) {
                    assert(sitePath.node == caller)
                    sitePath :: lst
                  } else {
                    if (Options.PRINT_REFS) println("refuted by return from call")
                    lst
                  }
                })
            }
          }})
        newPaths
      }
    } else // else callStack.size > 1, "normal" return from callee to caller
      p.callStack.top.callInstr match {
        case Some(callInstr) =>
          if (!p.returnFromCall(callInstr, callee, tf)) Nil
          else List(p)
        case None => sys.error("Expecting call instruction, but found nothing: " + p.callStack)
      }
  } ensuring (_.forall(newP => !(newP.callStackSize == 0)))
}