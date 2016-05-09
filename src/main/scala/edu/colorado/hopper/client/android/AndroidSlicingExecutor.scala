package edu.colorado.hopper.client.android

import com.ibm.wala.analysis.pointers.HeapGraph
import com.ibm.wala.ipa.callgraph.propagation.{InstanceKey, HeapModel}
import com.ibm.wala.ssa.{SSAGetInstruction, SSAInvokeInstruction}
import edu.colorado.hopper.executor.TransferFunctions
import edu.colorado.hopper.jumping.{DefaultJumpingSymbolicExecutor, RelevanceRelation}
import edu.colorado.hopper.state.Path
import edu.colorado.hopper.state._
import edu.colorado.hopper.util.PtUtil
//import edu.colorado.walautil.ClassUtil
//import com.ibm.wala.ipa.callgraph.propagation.{ConcreteTypeKey, HeapModel, InstanceKey, LocalPointerKey, PointerKey}


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
      //println("f "+iFld)
      //val heapSrc = Var.makeLPk(heapInstr.getDef(), caller, walaRes.hm)
      //ObjVar()//setInstanceKey
      //println(PtUtil.getPt(Var.makeLPK(heapInstr.getRef,caller,walaRes.hm),walaRes.hg))
      val instKeys = PtUtil.getPt(Var.makeLPK(heapInstr.getRef, caller, hm), hg)

      //PtEdge.make(null:HeapVar,iFld,ObjVar(PtUtil.getPt(receiver, walaRes.hg)))
      val hConstraint = PtEdge.make(ObjVar(instKeys), iFld, ObjVar(PtUtil.getPt(receiver, hg)))
      qry.addHeapConstraint(hConstraint)
      //println(hConstraint)
      //println(p)
      return doJump(p)

    } /*if(isEntrypointCallback(p.node,walaRes.cg)){
          if(p.getBackup){
            ???
          }else{
            super.returnFromCallNoJump(p)
          }
        }*/
    else {
      return super.returnFromCallNoJump(p)
    }
  }
}