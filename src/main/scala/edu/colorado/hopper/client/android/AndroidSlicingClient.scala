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
    val DROIDEL_HOME = "../droidel" // point this at your droidel install
    val DEBUG = true

  def makeExec() = {
    val rr = new AndroidRelevanceRelation(appTransformer, walaRes.cg, walaRes.hg, walaRes.hm, walaRes.cha)
    val tf = new JumpingTransferFunctions(walaRes.cg, walaRes.hg, walaRes.hm, walaRes.cha, rr)
    new AndroidSlicingExecutor(tf,rr,walaRes.hm,walaRes.hg)
  }


    override def check : (Int, Int) = {
        import walaRes._
        val exec = makeExec
        
        println("Looking for Invocation")

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
                    i.getDeclaredTarget.getSelector.getName.toString// + "(" + args + ")"
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
