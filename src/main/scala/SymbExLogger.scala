/**
 * Created by admin on 20.06.2015.
 */

package viper
package silicon

import java.io.File
import silver.ast
import interfaces.state.factoryUtils.Ø
import interfaces.state.{StateFactory, HeapFactory, Store}
import viper.silver.ast.Node



object SymbExLogger {
  var mpf_list = List[SymbLog]()

  def insert(mpf: silver.ast.Member, s: AnyRef): Unit ={
    // mpf: Method, Predicate or Function
    mpf_list = mpf_list ++ List(new SymbLog(mpf,s))
  }

  def currentLog(): SymbLog = {
    mpf_list.last
  }

  def writeDotFile(): Unit = {
    var str: String = "digraph {\n"
    str = str + "node [shape=rectangle];\n\n";

    for(mpf <- mpf_list) {
      str = str + mpf.toDot() + "\n\n"
    }

    str = str + "}"
    val pw = new java.io.PrintWriter(new File("dot_input.dot"))
    try pw.write(str) finally pw.close()
  }
}

//========================= SymbLog ========================

/*
 * Concept: One object of SymbLog per Method/Predicate/Function.
 */


class SymbLog(v: silver.ast.Member, s: AnyRef) {
  var main = v match {
    case m: silver.ast.Method     => new MethodRecord(m, s)
    case p: silver.ast.Predicate  => new PredicateRecord(p, s)
    case f: silver.ast.Function   => new FunctionRecord(f,s)
  }

  var stack = List[SymbolicRecord](main)
  var SEP_counter = 0
  var SEP_set = Set[Int]()

  def current(): SymbolicRecord = {
    stack.head
  }

  def insert(s: SymbolicRecord): Int = {

    if(!isUsed(s.value) || isRecordedDifferently(s))
      return -1

    current().subs = current().subs++List(s)
    stack = s::stack

    SEP_counter = SEP_counter+1
    SEP_set = SEP_set+SEP_counter
    return SEP_counter
  }

  def executor_insert(stmt: silver.ast.Stmt, s: AnyRef): Int ={
    var res = -1
    val v = new ExecuteRecord(stmt, s)
    res = insert(v)
    return res
  }

  def evaluator_insert(exp: silver.ast.Exp, s: AnyRef): Int ={
    var res = -1
    val v = new EvaluateRecord(exp, s)
    res = insert(v)
    return res
  }

  def producer_insert(exp: silver.ast.Exp, s: AnyRef): Int ={
    var res = -1
    val v = new ProduceRecord(exp, s)
    res = insert(v)
    return res
  }

  def consumer_insert(exp: silver.ast.Exp, s: AnyRef): Int ={
    var res = -1
    val v = new ConsumeRecord(exp, s)
    res = insert(v)
    return res
  }

  def collapse(v: silver.ast.Node, n: Int): Unit =
  {
    if(n != -1 && SEP_set.contains(n)) {
      SEP_set = SEP_set - n
      if (isUsed(v))
        stack = stack.tail
    }
  }

  def isRecordedDifferently(s: SymbolicRecord): Boolean =
  {
    s.value match {
      case v: silver.ast.MethodCall =>
        s match {
          case _: MethodCallRecord => false
          case _ => true
        }

      case _ => false
    }
  }

  def isUsed(node: silver.ast.Node): Boolean =
  {
    node match {
      case stmt: silver.ast.Stmt => {
        stmt match {
          case _: silver.ast.Seqn =>
            return false
          case _ =>
            return true
        }
      }
      case exp: silver.ast.Exp => {
        exp match {
          case _: ast.CondExp | /*_: ast.TrueLit | _: ast.FalseLit | _: ast.NullLit | _: ast.IntLit | _: ast.FullPerm | _: ast.NoPerm
               | _: ast.AbstractLocalVar |*/ _: ast.WildcardPerm | _: ast.FractionalPerm | _: ast.Result
               | _: ast.WildcardPerm | _: ast.FieldAccess =>
            return false
          case _ =>
            return true
        }
      }
      case _ => return true
    }
  }

  private var previousNode = "";
  private var unique_node_nr = this.hashCode();

  private def unique_node_number():Int = {
    unique_node_nr = unique_node_nr+1
    unique_node_nr
  }

  def toDot(): String = {

    var output = ""

    output = output + "    "+main.dotNode()+" [label="+main.dotLabel()+"];\n"
    output = output + subsToDot(main)
    output
  }

  private def subsToDot(s: SymbolicRecord):String =
  {
    previousNode = s.dotNode()

    var output = ""

    s match {
      case ite: IfThenElseRecord => {
        val ite_parent = previousNode
        output = output + "    " + ite.thnCond.dotNode() + " [label=" + ite.thnCond.dotLabel() + "];\n"
        output = output + "    " + previousNode + " -> " + ite.thnCond.dotNode() + ";\n"
        previousNode = ite.thnCond.dotNode()
        for (rec <- ite.thnSubs) {
          output = output + "    " + rec.dotNode() + " [label=" + rec.dotLabel() + "];\n"
          output = output + "    " + previousNode + " -> " + rec.dotNode() + ";\n"
          output = output + subsToDot(rec)
        }
        previousNode = ite_parent
        output = output + "    " + ite.elsCond.dotNode() + " [label=" + ite.elsCond.dotLabel() + "];\n"
        output = output + "    " + previousNode + " -> " + ite.elsCond.dotNode() + ";\n"
        previousNode = ite.elsCond.dotNode()
        for (rec <- ite.elsSubs) {
          output = output + "    " + rec.dotNode() + " [label=" + rec.dotLabel() + "];\n"
          output = output + "    " + previousNode + " -> " + rec.dotNode() + ";\n"
          output = output + subsToDot(rec)
        }
      }
      case ce: CondExpRecord => {

        output = output + "    " + ce.cond.dotNode() + " [label="+ce.cond.dotLabel()+"];\n"
        output = output + "    " + previousNode + " -> " + ce.cond.dotNode() + ";\n"
        previousNode = ce.cond.dotNode()

        output = output + "    " + ce.thnExp.dotNode() + " [label="+ce.thnExp.dotLabel()+"];\n"
        output = output + "    " + previousNode + " -> " + ce.thnExp.dotNode() + ";\n"
        output = output + subsToDot(ce.thnExp)
        val thnExp_end = previousNode

        previousNode = ce.cond.dotNode()
        output = output + "    " + ce.elsExp.dotNode() + " [label="+ce.elsExp.dotLabel()+"];\n"
        output = output + "    " + previousNode + " -> " + ce.elsExp.dotNode() + ";\n"
        output = output + subsToDot(ce.elsExp)
        val elsExp_end = previousNode

        val join_node = unique_node_number().toString()
        output = output + "    " + join_node + " [label=\"Join\"];\n"
        output = output + "    " + thnExp_end + " -> " + join_node + ";\n"
        output = output + "    " + elsExp_end + " -> " + join_node + ";\n"
        previousNode = join_node
      }

      case mc: MethodCallRecord => {
        val mc_parent = previousNode
        output = output + "    " + mc.dotNode() + " [label="+mc.dotLabel()+"];\n"
        previousNode = mc.dotNode()

        for(p <- mc.parameters){
          output = output + "    " + p.dotNode() + " [label=\"parameter: "+p.toSimpleString()+"\"];\n"
          output = output + "    " + previousNode + " -> " + p.dotNode() + ";\n"
          output = output + subsToDot(p)
        }
        previousNode = mc.dotNode()

        output = output + "    " + mc.precondition.dotNode() + " [label=\"precondition: "+mc.precondition.toSimpleString()+"\"];\n"
        output = output + "    " + previousNode + " -> " + mc.precondition.dotNode() + ";\n"
        output = output + subsToDot(mc.precondition)
        previousNode = mc.dotNode()

        output = output + "    " + mc.postcondition.dotNode() + " [label=\"postcondition: "+mc.postcondition.toSimpleString()+"\"];\n"
        output = output + "    " + previousNode + " -> " + mc.postcondition.dotNode() + ";\n"
        output = output + subsToDot(mc.postcondition)
        previousNode = mc.dotNode()


      }
      case _ => {
        if(s.subs.isEmpty)
          return ""
        for(rec <- s.subs) {
          output = output + "    " + rec.dotNode() + " [label=" + rec.dotLabel() + "];\n"
          output = output + "    " + previousNode + " -> " + rec.dotNode() + ";\n"
          output = output + subsToDot(rec)
        }
      }
    }

    return output
  }


}

//=========================

trait SymbolicRecord {
  val value: silver.ast.Node
  val state: AnyRef
  var subs = List[SymbolicRecord]()

  override def toString():String = {
    if(value != null)  value.toString()
    else "null"
  }

  def toSimpleString():String = {
    if(value != null)  value.toString()
    else "null"
  }

  def toSimpleTree(n: Int):String = {
    var ident = ""
    for(i <- 1 to n) {
      ident = "  " + ident
    }
    var str:String = this.toString()+"\n"
    for(s <- subs){
      str = str + ident + s.toSimpleTree(n+1)
    }
    str
  }

  def dotNode(): String = {
    this.hashCode().toString()
  }

  def dotLabel(): String = {
    "\""+this.toString()+"\""
  }
}

class MethodRecord(v: silver.ast.Method, s: AnyRef) extends SymbolicRecord {
  val value = v
  val state = s

  override def toString():String = {
    "method " + toSimpleString()
  }

  override def toSimpleString():String = {
    if(value != null) value.name
    else "null"
  }
}

class PredicateRecord(v: silver.ast.Predicate, s: AnyRef) extends SymbolicRecord {
  val value = v
  val state = s

  override def toString():String = {
    "predicate "+toSimpleString()
  }

  override def toSimpleString():String = {
    if(value != null) value.name
    else "null"
  }
}

class FunctionRecord(v: silver.ast.Function, s: AnyRef) extends SymbolicRecord {
  val value = v
  val state = s

  override def toString():String = {
    "function "+toSimpleString()
  }

  override def toSimpleString():String = {
    if(value != null) value.name
    else "null"
  }
}

class ExecuteRecord(v: silver.ast.Stmt, s: AnyRef) extends SymbolicRecord {
  val value = v
  val state = s

  override def toString():String = {
    "execute: "+toSimpleString()
  }
}

class EvaluateRecord(v: silver.ast.Exp, s: AnyRef) extends SymbolicRecord {
  val value = v
  val state = s

  override def toString():String = {
    "evaluate: "+toSimpleString()
  }
}

class ProduceRecord(v: silver.ast.Exp, s: AnyRef) extends SymbolicRecord {
  val value = v
  val state = s

  override def toString():String = {
    "produce: "+toSimpleString()
  }
}

class ConsumeRecord(v: silver.ast.Exp, s: AnyRef) extends SymbolicRecord {
  val value = v
  val state = s

  override def toString():String = {
    "execute: "+toSimpleString()
  }
}

class IfThenElseRecord(v: silver.ast.Exp, s: AnyRef) extends SymbolicRecord {
  val value = v //meaningless
  val state = s

  var thnCond:SymbolicRecord = new EvaluateRecord(null, null)
  var elsCond:SymbolicRecord = new EvaluateRecord(null, null)

  var thnSubs = List[SymbolicRecord](new CommentRecord("Unreachable", null))
  var elsSubs = List[SymbolicRecord](new CommentRecord("Unreachable", null))

  override def toString(): String ={
    "if "+thnCond.toSimpleString()
  }

  override def toSimpleString(): String = {
    "if "+thnCond.toSimpleString()
  }

  override def toSimpleTree(n: Int): String ={
    var ident = ""
    for(i <- 1 to n) {
      ident = "  " + ident
    }

    var str = ""
    str = str + "if " + thnCond.value.toString()+":\n"
    str = str + ident + thnCond.toSimpleTree(n+1)
    for(s <- thnSubs){
      str = str + ident + s.toSimpleTree(n+1)
    }

    str = str + ident.substring(2) + "else " + elsCond.value.toString()+":\n"
    str = str + ident + elsCond.toSimpleTree(n+1)
    for(s <- elsSubs){
      str = str + ident + s.toSimpleTree(n+1)
    }
    return str
  }
}

class CondExpRecord(v: silver.ast.Exp, s: AnyRef) extends SymbolicRecord {
  val value = v
  val state = s

  var cond:SymbolicRecord   = new EvaluateRecord(null, null)
  // thn/els Exp is Unreachable by default. If this is not the case, it will be overwritten
  var thnExp:SymbolicRecord = new CommentRecord("Unreachable", null)
  var elsExp:SymbolicRecord = new CommentRecord("Unreachable", null)

  override def toString(): String = {
    "evaluate: "+cond.toSimpleString() + " ? " + thnExp.toSimpleString() + " : " + elsExp.toSimpleString()
  }

  override def toSimpleString(): String = {
    "(" + cond.toSimpleString() + " ? " + thnExp.toSimpleString() + " : " + elsExp.toSimpleString() + ")"
  }

  override def toSimpleTree(n: Int):String = {
    var ident = ""
    for(i <- 1 to n) {
      ident = "  " + ident
    }
    var str = ""
    str = str + toString()+"\n"
    str = str + ident + thnExp.toSimpleTree(n+1)
    str = str + ident + elsExp.toSimpleTree(n+1)
    return str
  }
}

class CommentRecord(str: String, s: AnyRef) extends SymbolicRecord {
  val value = null
  val state = s

  val comment = str

  override def toSimpleString(): String = {
    if(comment != null) comment
    else "null"
  }

  override def toString(): String = {
    "comment: " + toSimpleString()
  }

  override def dotLabel():String = {
    "\""+comment+"\""
  }
}

class MethodCallRecord(v: silver.ast.MethodCall, s: AnyRef) extends SymbolicRecord {
  val value = v
  val state = s

  var parameters = List[SymbolicRecord]()

  var precondition: SymbolicRecord = new ConsumeRecord(null,null)
  var postcondition:SymbolicRecord = new ProduceRecord(null,null)

  override def toSimpleTree(n: Int):String = {
    var ident = ""
    for(i <- 1 to n) {
      ident = "  " + ident
    }
    var str = ""
    str = str + toString()+"\n"
    str = str + ident + "precondition: " + precondition.toSimpleTree(n+1)
    str = str + ident + "postcondition: " + postcondition.toSimpleTree(n+1)
    for(p <- parameters) {
      str = str + ident + "parameter: " + p.toSimpleTree(n+1)
    }
    return str
  }

  override def toString(): String ={
    if(v != null)
      "execute: " + v.toString()
    else
      "execute: MethodCall <null>"
  }

  override def toSimpleString(): String = {
    if(v != null) v.toString()
    else "MethodCall <null>"
  }
}

