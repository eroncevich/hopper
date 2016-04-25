package edu.colorado.hopper.state

import com.ibm.wala.classLoader.IMethod.SourcePosition

import scala.collection.mutable

abstract class NonReducibleVal (){
    
}
case class PrimitiveVal(c:AnyVal,loc : SourcePosition) extends NonReducibleVal{ //Includes all numbers/bools/chars/etc
    override def toString = c.toString
}
case class Variable(ssa_num : Int) extends NonReducibleVal{ //contains the id of the variable
    override def toString = s"v$ssa_num"
}
case class FrameworkFun(methodName: String, loc : SourcePosition){

}

/** The Dependency Event is a linked list of Dependency Trees, where a new tree is
  * created for each change of events*/
class DependencyEvents(){
    var currTree = DependencyTree(mutable.HashMap():collection.mutable.HashMap[NonReducibleVal,List[(NonReducibleVal,FrameworkFun)]])
    var eventTrees:List[DependencyTree] = List()
    def pushDepTree() ={
        eventTrees = eventTrees ::: List(currTree)
        currTree = DependencyTree(mutable.HashMap():collection.mutable.HashMap[NonReducibleVal,List[(NonReducibleVal,FrameworkFun)]])
    }
    def addEdge(v1: NonReducibleVal, v2: NonReducibleVal, f:FrameworkFun) = {
        currTree.addEdge(v1,v2,f)
    }
    override def clone(): DependencyEvents = {
        val de = new DependencyEvents
        de.currTree = currTree.clone()
        de.eventTrees = eventTrees.foldLeft(List():List[DependencyTree]){(a,t) => a:::List(t.clone())}
        de
    }
    override def toString = "currTree: "+currTree+"\n" + eventTrees.toString
}

/** A hashtable of NonReducibleVals dependent on other NonReducibleVals
  * The graph is a relation of (v2,v1) where v1 is dependent of v2 when
  * going through a function in the framework (e.g. v1.f(v2)) */
case class DependencyTree(depTable:collection.mutable.HashMap[NonReducibleVal,List[(NonReducibleVal,FrameworkFun)]]){
    
    def addEdge(v1: NonReducibleVal, v2: NonReducibleVal, f: FrameworkFun) = { //add new Edge at node v1
        if(depTable.contains(v1)) {
            depTable += (v1 -> (depTable(v1) ::: List((v2, f))))
        }else{
            depTable += (v1 -> List((v2, f)))
        }
    }
    override def clone(): DependencyTree = {
        return new DependencyTree(depTable.clone())
    }
    override def equals(o: Any): Boolean = o match {
        case DependencyTree(dt) => depTable == dt
        case _ => false
    }

}
