package edu.colorado.hopper.client.android

import java.io.File
import java.util

import com.ibm.wala.analysis.pointers.HeapGraph
import com.ibm.wala.ipa.callgraph.propagation.{PointerKey, InstanceKey, HeapModel}
import com.ibm.wala.util.intset.OrdinalSet
import edu.colorado.hopper.client.android.AndroidUtil._
import edu.colorado.walautil.Timer
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
      val tf = new TransferFunctions(walaRes.cg, walaRes.hg, walaRes.hm, walaRes.cha)


      new AndroidJumpingSymbolicExecutor(tf, rr) {

        override def returnFromCall(p : Path) : Iterable[Path] =
          if (p.callStackSize == 1 && !p.node.getMethod.isInit) {
            val qry = p.qry
            // keep one constraint on null and the access path to the constraint--drop all other constraints
            qry.heapConstraints.find(e => e.snk match {
              case p@PureVar(t) if t.isReferenceType => qry.isNull(p)
              case _ => false
            }) match {
              case Some(e) =>
                val keepEdges = qry.getAccessPrefixPathFor(e)
                val shouldJump =
                  isEntrypointCallback(p.node, cg) || {
                    e match {
                      case ObjPtEdge(_, InstanceFld(fld), _) =>
                        val keepEdges = qry.getAccessPrefixPathFor(e)
                        // guaranteed to exist because getAccessPathPrefix returns at least e
                        val accessPathHead = keepEdges.head.src
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
                else { // have access path originating from this or at entrypoint callback, jump
                  if (DEBUG) println(s"have complete access path or at function boundary of entrypoint cb ${p.node}")
                  // weaken query by removing all constraints but access path, then jump
                  qry.heapConstraints.foreach(e => if (!keepEdges.contains(e)) qry.removeHeapConstraint(e))
                  doJump(p)
                }
              case None =>
                // keep entire query
                if (isEntrypointCallback(p.node, cg)) { // at function of entrypoint callback--we should jump
                  if (DEBUG) println(s"at function boundary of entrypoint cb ${p.node}")
                  doJump(p)
                } else super.returnFromCallNoJump(p)
            }
          } else super.returnFromCallNoJump(p)

        //override def handleEmptyCallees(paths : List[Path], i : SSAInvokeInstruction, caller : CGNode) : List[Path] =
          //handleEmptyCalleesImpl(paths, i, caller, tf.hm)

      }
    }
  def makeTF(rr : RelevanceRelation) = new TransferFunctions(walaRes.cg,walaRes.hg,walaRes.hm,walaRes.cha){//NullDereferenceTransferFunctions(walaRes, new File(s"$appPath/nit_annots.xml")) {

    def useMayBeRelevantToQuery(use : Int, qry : Qry, n : CGNode, hm : HeapModel,
                                hg : HeapGraph[InstanceKey]) : Boolean = {
      val tbl = n.getIR.getSymbolTable
      !tbl.isConstant(use) && {
        val lpk = Var.makeLPK(use, n, hm)
        qry.localConstraints.exists(e => e.src.key == lpk) || {
          val queryInstanceKeys = qry.getAllObjVars.flatMap(o => o.rgn)
          queryInstanceKeys.intersect(PtUtil.getPt(lpk, hg)).nonEmpty || qry.localMayPointIntoQuery(lpk, n, hm, hg, cha)
        }
      }
    }

//    def isNullConstraint(cond : SSAConditionalBranchInstruction, n : CGNode) : Boolean = {
//      val tbl = n.getIR.getSymbolTable
//      tbl.isNullConstant(cond.getUse(0)) || tbl.isNullConstant(cond.getUse(1))
//    }

    /** @return true if we should add the conditional expression from @param cond as a constraint given that we want to
      * refute @param qry, false otherwise */
    def shouldAddConditionalConstraint(cond : SSAConditionalBranchInstruction, qry : Qry, n : CGNode) : Boolean = {
      val shouldAdd =
        useMayBeRelevantToQuery(cond.getUse(0), qry, n, hm, hg) ||
          useMayBeRelevantToQuery(cond.getUse(1), qry, n, hm, hg)
      if (DEBUG && !shouldAdd) {
        print("Not adding cond "); ClassUtil.pp_instr(cond, n.getIR); println(" since it may be irrel")
      }
      shouldAdd
    }

    override def isCallRelevant(i : SSAInvokeInstruction, caller : CGNode, callee : CGNode, qry : Qry) : Boolean =
      if (Options.JUMPING_EXECUTION)
        isRetvalRelevant(i, caller, qry) ||
          JumpingTransferFunctions.doesCalleeModifyHeap(callee, qry, rr, cg,
            getReachable = getReachableInAndroidCG)
      else super.isCallRelevant(i, caller, callee, qry)

    override def dropCallConstraints(qry : Qry, callee : CGNode,
                                     modRef : util.Map[CGNode,OrdinalSet[PointerKey]],
                                     loopDrop : Boolean) : Unit =
      if (Options.JUMPING_EXECUTION)
        JumpingTransferFunctions.dropCallConstraints(qry, callee, rr, cg,
          getReachable = getReachableInAndroidCG)
      else super.dropCallConstraints(qry, callee, modRef, loopDrop)

    override def executeCond(cond : SSAConditionalBranchInstruction, qry : Qry, n : CGNode,
                             isThenBranch : Boolean) : Boolean =
    // decide whether or not we should keep the condition
      if (shouldAddConditionalConstraint(cond, qry, n)) super.executeCond(cond, qry, n, isThenBranch)
      else true
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
          new DefaultJumpingSymbolicExecutor(tf,rr)
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
