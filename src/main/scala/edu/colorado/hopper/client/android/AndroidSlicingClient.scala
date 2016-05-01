package edu.colorado.hopper.client.android

import java.io.File
import java.util

import com.ibm.wala.analysis.pointers.HeapGraph
import com.ibm.wala.ipa.callgraph.propagation.{PointerKey, InstanceKey, HeapModel}
import com.ibm.wala.util.intset.OrdinalSet
import edu.colorado.hopper.client.android.AndroidUtil._
import edu.colorado.walautil.Timer
import com.ibm.wala.ipa.callgraph._
import edu.colorado.hopper.state._

import edu.colorado.hopper.executor._


//others
import edu.colorado.walautil._
import com.ibm.wala.ipa.callgraph.{AnalysisCache, AnalysisOptions, AnalysisScope, CallGraph,CGNode}
import scala.collection.JavaConversions._
//import com.ibm.wala.types.TypeReference


import edu.colorado.hopper.client.{ClientTests, NullDereferenceTransferFunctions}
import edu.colorado.hopper.jumping.{DefaultJumpingSymbolicExecutor, JumpingTransferFunctions, RelevanceRelation}
import edu.colorado.hopper.solver.{ThreadSafeZ3Solver, Z3Solver}


import edu.colorado.hopper.util.PtUtil
import edu.colorado.hopper.client.android._


import com.ibm.wala.ssa._
import edu.colorado.thresher.core.Options

class AndroidSlicingClient(appPath: String, sensitiveMethod: String, androidLib: File, useJPhantom: Boolean = true)
    extends DroidelClient[(Int,Int)](appPath, androidLib, useJPhantom){
                       
    Options.JUMPING_EXECUTION = true
    Options.CONTROL_FEASIBILITY = true
    val one = 1
    val DROIDEL_HOME = "../droidel" // point this at your droidel install
    val DEBUG = true

  def makeExec() = {
    val rr = new AndroidRelevanceRelation(appTransformer, walaRes.cg, walaRes.hg, walaRes.hm, walaRes.cha)
    val tf = new JumpingTransferFunctions(walaRes.cg, walaRes.hg, walaRes.hm, walaRes.cha, rr)
    new AndroidJumpingSymbolicExecutor(tf, rr) {

      override def returnFromCall(p: Path): Iterable[Path] = {
        println("retrnFromCall")
        if(p.qry.node.getMethod.toString=="< Primordial, Landroid/view/View, performClick()Z >"){
        }
        if(p.qry.node.getMethod.toString=="< Application, Lcom/plv/evan/sensitiveunit1/unit$1, onClick(Landroid/view/View;)V >"){
          val qry = p.qry
          val caller = getCallers(walaRes.cg,qry.node).head
          println(caller)
          val instrs =caller.getIR.getInstructions.filter{ i => i match{
            case ii:SSAInvokeInstruction =>cg.getPossibleTargets(caller, ii.getCallSite()).contains(qry.node)
            case _=> false
          }}
          val heapInstrs = caller.getIR.getInstructions.find{i=>i match{
            case ii:SSAGetInstruction => i.iindex==17
            case _=>false
          }}
          val heapInstr = heapInstrs match{
            case Some(i:SSAGetInstruction) => i
            case _ => throw new ClassCastException
          }

          val instr = instrs.head match{
            case i:SSAInvokeInstruction => i
            case _ => throw new ClassCastException
          }
          println(instr)
          val invokeUse = instr.getDef
          val receiver = Var.makeLPK(1,qry.node,walaRes.hm)
          val iFld = cha.resolveField(heapInstr.getDeclaredField)
          println("f "+iFld)
          //val heapSrc = Var.makeLPk(heapInstr.getDef(), caller, walaRes.hm)
          //ObjVar()//setInstanceKey
          println(PtUtil.getPt(Var.makeLPK(heapInstr.getRef,caller,walaRes.hm),walaRes.hg))
          val instKeys = PtUtil.getPt(Var.makeLPK(heapInstr.getRef,caller,walaRes.hm),walaRes.hg)

          //PtEdge.make(null:HeapVar,iFld,ObjVar(PtUtil.getPt(receiver, walaRes.hg)))
          val hConstraint = PtEdge.make(ObjVar(instKeys),iFld,ObjVar(PtUtil.getPt(receiver, walaRes.hg)))
          qry.addHeapConstraint(hConstraint)
          println(hConstraint)
          println(p)
          return doJump(p)


          /*val jumpSet = walaRes.hg.getPointerAnalysis.getPointsToSet(receiver)
          for(j<-jumpSet){
            val sites = j.getCreationSites(walaRes.cg).toList
            for(s<- sites){
              println(s.fst)
              println(s.snd)
              println(s.fst.getIR.getNew(s.snd))
              val newInstr = s.fst.getIR.getNew(s.snd)
              //< Primordial, Landroid/view/View, mListenerInfo, <Primordial,Landroid/view/View$ListenerInfo>
              //PtEdge.make(null:HeapVar,null:Fld,ObjVar(PtUtil.getPt(receiver, walaRes.hg)))
              //ObjPtEdge(ObjVar(Var.makeLPK(10,caller,walaRes.hm)),heapInstr.getDeclaredField,ObjVar(PtUtil.getPt(receiver, walaRes.hg)))
              //println(PtUtil.get(ObjVar(PtUtil.getPt(receiver, walaRes.hg)),walaRes.hg))
              //PtUtil.get(PtEdge.make(receiver, ObjVar(PtUtil.getPt(receiver, walaRes.hg))),walaRes.hm)
            }

          }*/
          //PtEdge.make(ObjVar(jumpSet.toSet),???:Field,???:Val)
          throw WitnessFoundException
        }else{return super.returnFromCallNoJump(p)}
/*
        if (p.callStackSize == 1 && !p.node.getMethod.isInit) {
          val qry = p.qry
          // keep one constraint on null and the access path to the constraint--drop all other constraints
          println(qry.node)
          qry.heapConstraints.find(e => true) match {
            case Some(e) =>
              val keepEdges = qry.getAccessPrefixPathFor(e)
              val shouldJump =
                isEntrypointCallback(p.node, cg) || {
                  e match {
                    case ObjPtEdge(_, InstanceFld(fld), _) =>
                      val keepEdges = qry.getAccessPrefixPathFor(e)
                      // guaranteed to exist because getAccessPathPrefix returns at least e
                      val accessPathHead = keepEdges.head.src
                      println("E::" + e)
                      println(accessPathHead)
                      // see if the access path leading to the null constraint is rooted in a function parameter other
                      // than "this". if this is the case, we want to keep going backward without jumping in order to
                      // get a more complete access path to the null constraint
                      val accessPathRootedInNonThisParam =
                        qry.localConstraints.exists(e => e match {
                          case LocalPtEdge(LocalVar(key), snk) =>
                            snk == accessPathHead && !IRUtil.isThisVar(key.getValueNumber)
                          case _ => false
                        })
                      def someCallerMayReadOrWriteFld(): Boolean = cg.getPredNodes(p.node).exists(n => n.getIR match {
                        case null => false
                        case ir =>
                          val fldRef = fld.getReference
                          ir.iterateAllInstructions().exists(i => i match {
                            case i: SSAFieldAccessInstruction => i.getDeclaredField == fldRef
                            case _ => false
                          })
                      })
                      // don't jump if the access path is not rooted in this or if a caller may read/write the field
                      // that points to nul
                      !accessPathRootedInNonThisParam && !someCallerMayReadOrWriteFld
                    case _ => false
                  }
                }
              if (!shouldJump) super.returnFromCallNoJump(p)
              else {
                // have access path originating from this or at entrypoint callback, jump
                if (DEBUG) println(s"have complete access path or at function boundary of entrypoint cb ${p.node}")
                // weaken query by removing all constraints but access path, then jump
                qry.heapConstraints.foreach(e => if (!keepEdges.contains(e)) qry.removeHeapConstraint(e))
                doJump(p)
              }
            case None =>
              // keep entire query
              if (isEntrypointCallback(p.node, cg)) {
                // at function of entrypoint callback--we should jump
                if (DEBUG) println(s"at function boundary of entrypoint cb ${p.node}")
                doJump(p)
              } else super.returnFromCallNoJump(p)
          }
        } else super.returnFromCallNoJump(p)*/

        //override def handleEmptyCallees(paths : List[Path], i : SSAInvokeInstruction, caller : CGNode) : List[Path] =
        //handleEmptyCalleesImpl(paths, i, caller, tf.hm)
      }
    }
  }


    override def check : (Int, Int) = {
        import walaRes._       

        val exec = {
          val rr = new AndroidRelevanceRelation(appTransformer, walaRes.cg, walaRes.hg, walaRes.hm, walaRes.cha)
          //val rr = new RelevanceRelation(walaRes.cg, walaRes.hg, walaRes.hm, walaRes.cha)
          val tf = new JumpingTransferFunctions(walaRes.cg, walaRes.hg, walaRes.hm, walaRes.cha, rr)
          //val tf = new TransferFunctions(walaRes.cg, walaRes.hg, walaRes.hm, walaRes.cha)
          //val tf = makeTF(rr)
          //new AndroidJumpingSymbolicExecutor(tf,rr)
          //new DefaultJumpingSymbolicExecutor(tf,rr)
          makeExec()
        }

        
        println("TRANSFER")


        val invokeInst =
      walaRes.cg.foldLeft (List.empty[(Int,CGNode)]) ((l, n) => // for each node n in the call graph
        if (shouldCheck(n)) n.getIR match { // don't analyze library code
          case null =>l
          case ir => // for each instruction in the IR for the call graph node
            println(ClassUtil.pretty(n.getMethod()))
            val tbl = ir.getSymbolTable
            
            ir.getInstructions.zipWithIndex.foldLeft(l)((l, pair) => {
              val (i, index) = pair
              //println(i)
              i match {
                case i: SSAInvokeInstruction =>
                  val args = (0 to i.getDeclaredTarget.getNumberOfParameters-1).foldLeft("") { (a, ind) => {
                    val arg = i.getDeclaredTarget.getParameterType(ind).getName.toString
                    if (a == "") arg
                    else arg + "," + arg
                  }
                  }
                  val funStr = i.getDeclaredTarget.getDeclaringClass.getName.toString +"." +
                    i.getDeclaredTarget.getSelector.getName.toString + "(" + args + ")"
                  //println(sensitiveMethod == funStr)
                  //if(i.getCallSite.getDeclaredTarget.toString == "< Application, Lcom/plv/evan/sensitiveunit1/unit, sensitiveMethod()V >"){
                  if(sensitiveMethod==funStr){

                      println(s"Found ${i.getCallSite.getDeclaredTarget}");
                      val srcLine = IRUtil.getSourceLine(i, ir)
                      print("Checking invoke instruction "); ClassUtil.pp_instr (i, ir); println(s" at line $srcLine")
                      val invokeUse = i.getReceiver
                      println(s"invoke use: ${invokeUse}")
                      // query: z |-> p ^ p = 0
                      val receiver = Var.makeLPK(invokeUse, n, walaRes.hm)
                      val receiverPtNonNull = PtEdge.make(receiver, ObjVar(PtUtil.getPt(receiver, hg)))
                      val reachable ={
                          //val qry = Qry.make(List(receiverPtNonNull), i, n, walaRes.hm, startBeforeI = true)
                          val qry = Qry.make(List(), i, n, walaRes.hm, startBeforeI = true)
                          println(s"The initial qry is ${qry}")
                          try{
                                val mayBeFeasible = exec.executeBackward(qry)
                                !mayBeFeasible //
                          }catch{
                              case BudgetExceededException =>
                                println("Budget Exceeded")
                              case e : Throwable =>
                                println(s"Error on access $e \n${e.getStackTraceString}")
                                throw e
                          }
                          true
                      }
                      println(s"Is reachable? ${reachable}")
                      
                      (index, n) :: l
                  }
                  else l
                case _ => l
              }
            })
        } else l
      )
        
        
        
        return (1,1)
    }
    def shouldCheck(n : CGNode) : Boolean = {
      // check Options allows us to restrict analysis to a particular class or method
      val checkClass =
        if (Options.MAIN_CLASS == "Main") true
        else n.getMethod.getDeclaringClass.getName.toString.contains(Options.MAIN_CLASS)
      val checkMethod =
        if (Options.MAIN_METHOD == "main") true else n.getMethod.getName.toString == Options.MAIN_METHOD
      checkClass && checkMethod && !ClassUtil.isLibrary(n)
    }
    
    
    

    
}
