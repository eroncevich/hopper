package edu.colorado.hopper.client.android

import com.ibm.wala.analysis.pointers.HeapGraph
import com.ibm.wala.ipa.callgraph.CGNode
import com.ibm.wala.ipa.callgraph.propagation.{InstanceKey, HeapModel}
import com.ibm.wala.ssa._
import edu.colorado.hopper.executor.TransferFunctions
import edu.colorado.hopper.jumping.{DefaultJumpingSymbolicExecutor, RelevanceRelation}
import edu.colorado.hopper.state.Path
import edu.colorado.hopper.state._
import edu.colorado.hopper.util.PtUtil
import edu.colorado.walautil.ClassUtil

import scala.io.Source


/**
  * Created by evan on 5/9/16.
  */
class AndroidSlicingExecutor(tf: TransferFunctions, rr: RelevanceRelation, hm: HeapModel, hg: HeapGraph[InstanceKey])
  extends AndroidJumpingSymbolicExecutor(tf, rr) {

  override def returnFromCall(p: Path): Iterable[Path] = {
    println("retrnFromCall")
    if (p.qry.node.getMethod.getSelector.getName.toString == "onCreate") {
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
      return super.returnFromCallNoJump(p)
    }
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
}