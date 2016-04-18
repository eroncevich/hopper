package edu.colorado.hopper.state

import com.ibm.wala.classLoader.IMethod.SourcePosition

case class NRid(sp: SourcePosition){
    
}

abstract class NonReducibleVal (){
    
}
case class FrameworkFun(name:String, loc : SourcePosition) extends NonReducibleVal{ //need parameter for location in code
    override def toString = name
}
case class NonFrameworkFun(name:String,loc : SourcePosition) extends NonReducibleVal{ //need parameter for location in code
    override def toString = name
}

case class PrimitiveVal(c:AnyVal,loc : SourcePosition) extends NonReducibleVal{ //Includes all numbers/bools/chars/etc
    override def toString = c.toString
}
case class Variable(ssa_num : Int, loc : SourcePosition) extends NonReducibleVal{ //contains the id of the variable
    override def toString = s"v$ssa_num"
}
case class Empty() extends NonReducibleVal{ //An empty Dependency
}
case class DependencyTree(depTable:collection.mutable.HashMap[NonReducibleVal,List[NonReducibleVal]]){
    val leafs = collection.mutable.Set[NonReducibleVal]()
    //println(leafs)
    for( e <- depTable ) {
        for (v <- e._2){
            if(! depTable.contains(v)){
                //if(Options.DEBUG) println(v)
                leafs+=v
            }
        }
    }
    //println(leafs)
    //def leafs = depTable.keys - depTable.

    def deps(): List[NonReducibleVal] = { //return leaf nodes
        leafs.toList
    }
    
    def replace(x: Variable, v: NonReducibleVal) = {  //replace leaf node with new dependency tree (D[v/x])
        x match {
            case Variable(_,_) =>
            case _ => throw new IllegalArgumentException
        }
        for(e <- depTable) {
            if(e._2.contains(x)){
                depTable+= (e._1 -> e._2.foldLeft(List():List[NonReducibleVal]){(a,vi)=> if(vi==x) a++List(v) else a++List(vi)})
                if(leafs.contains(e._1)) leafs-= e._1
                leafs+=v
            }
        }
    }
    
    def addEdge(v1: NonReducibleVal, v2: NonReducibleVal) = { //add new Edge at node v1
        //check if entry exists
        if(depTable.contains(v1)){
            depTable+= (v1->(depTable(v1) ++ List(v2)))
            if(leafs.contains(v1)) leafs-= v1
        }else{
            throw new IllegalArgumentException
        }
        leafs+=v2
    }
    def getRoot():List[NonReducibleVal] ={
        depTable.foldLeft(List():List[NonReducibleVal]){(a,v) => v._1 match{
            case Empty() => a:::v._2
            case _ => a
            }}
    }
    override def clone(): DependencyTree = {
        return new DependencyTree(depTable.clone())
    }
    override def equals(o: Any): Boolean = o match {
        case DependencyTree(dt) => depTable == dt
        case _ => false
    }

}
