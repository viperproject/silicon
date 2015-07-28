/**
 * Created by admin on 20.06.2015.
 */

package viper
package silicon

import java.io.File
import silver.ast
import interfaces.state.factoryUtils.Ø
import interfaces.state.{StateFactory, HeapFactory, Store}
import viper.silicon.state.DefaultContext
import viper.silver.ast.Node

/*
 * Overall concept:
 * 1) SymbExLogger Object:
 *    Is used as interface to access the logs. Contains a list of SymbLog, one SymbLog
 *    per method/function/predicate (mpf). The method 'currentLog()' gives access to the log
 *    of the currently executed mpf. Code from this file that is used in Silicon should only be used
 *    via SymbExLogger.
 * 2) SymbLog:
 *    Contains the log for one mpf. Most important methods: insert/collapse. To 'start'
 *    a record use insert, to finish the recording use collapse. There should be as many calls
 *    of collapse as of insert (theoretically; practically this is not possible due to branching.
 *    To avoid such cases, each insert gets an identifier, which is then used by collapse, to avoid
 *    multiple collapses per insert).
 * 3) Records:
 *    The basic abstract record type is SymbolicRecord. There is one record type for each of the
 *    four basic symbolic primitives evaluate, execute, consume and produce. For constructs of special
 *    interest (e.g., if-then-else-branching), there are separate records.
 *    The basic record looks conceptually as follows:
 *
 *    SymbolicRecord {
 *      subs = List[SymbolicRecord]
 *    }
 *
 *    Example to illustrate the way a silver program is logged:
 *    Assume the following silver code:
 *
 *    method m() {
 *      var a: Int
 *      a := 1
 *      a := a+2
 *    }
 *
 *    This results in a log that can be visualized as a simple tree (see: toSimpleTree()) as follows:
 *
 *    method m
 *      execute a := 1
 *        evaluate 1
 *      execute a := a + 2
 *        evaluate a
 *        evaluate 2
 *
 *    The order of insert/collapse is as follows:
 *    insert(method), insert(execute), insert (evaluate),
 *    collapse(evaluate), collapse(execute),
 *    insert(execute), insert(evaluate) collapse(evaluate),
 *    insert(evaluate), collapse(evaluate)
 *    collapse(execute), collapse(method)
 *
 *    Collapse basically 'removes one indentation', i.e., brings you one level higher in the tree.
 *    For an overview of 'custom' records (e.g., for Branching, local branching, method calls etc.),
 *    have a look at the bottom of this file for a guide in how to create such records or take a look
 *    at already existing examples such as IfThenElseRecord, CondExpRecord or MethodCallRecord.
 */



object SymbExLogger {
  /** List of logged Method/Predicates/Functions. **/
  var mpf_list = List[SymbLog]()

  /** Add a new log for a method, function or predicate (mpf).
   *
   * @param mpf Either a MethodRecord, PredicateRecord or a FunctionRecord.
   * @param s Current state. Since the body of the method (predicate/function) is not yet
   *          executed/logged, this is usually the empty state (use Σ(Ø, Ø, Ø) for empty
   *          state).
   * @param c Current context.
   */
  def mpf_insert(mpf: silver.ast.Member, s: AnyRef, c: DefaultContext): Unit ={
    mpf_list = mpf_list ++ List(new SymbLog(mpf, s, c))
  }

  /** Use this method to access the current log, e.g., to access the log of the method
    * that gets currently symbolically executed.
   *
   * @return Returns the current method, predicate or function that is being logged.
   */
  def currentLog(): SymbLog = {
    mpf_list.last
  }

  /**
   * Simple string representation of the logs.
   */
  def simpleTreeString():String = {
    var res = ""
    for (mpf <- mpf_list){
      res = res + mpf.main.toSimpleTree(1) + "\n"
    }
    res
  }

  /**
   * Simple string representation of the logs, but contains only the types of the records
   * and not their values. Original purpose was usage for unit testing.
   */
  def typeTreeString():String = {
    var res = ""
    for (mpf <- mpf_list){
      res = res + mpf.main.toTypeTree(1) + "\n"
    }
    res
  }
  /**
   * Writes a .DOT-file with a representation of all logged methods, predicates, functions.
   * DOT-file can be interpreted with GraphViz (http://www.graphviz.org/)
   */
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

  def writeJSFile(): Unit = {
    val pw = new java.io.PrintWriter(new File("executionTreeData.js"))
    try pw.write(printJSTree()) finally pw.close()
  }

  def printJSTree(): String = {
    var str = "var executionTreeData = [\n"
    for(mpf <- mpf_list) {
      str = str + mpf.toJSTree() + ", \n"
    }
    str = str + "]\n"
    return str
  }
}

//========================= SymbLog ========================

/**
 * Concept: One object of SymbLog per Method/Predicate/Function. SymbLog
 * is used in the SymbExLogger-object.
 */
class SymbLog(v: silver.ast.Member, s: AnyRef, c: DefaultContext) {
  var main = v match {
    case m: silver.ast.Method     => new MethodRecord(m, s, c)
    case p: silver.ast.Predicate  => new PredicateRecord(p, s, c)
    case f: silver.ast.Function   => new FunctionRecord(f,s, c)
  }

  private var stack = List[SymbolicRecord](main)
  private var SEP_counter = 0
  private var SEP_set = Set[Int]()

  private def current(): SymbolicRecord = {
    stack.head
  }

  /**
   * Inserts a record. For usage of custom records, take a look at the guidelines in SymbExLogger.scala.
   * For every insert, there MUST be a call of collapse at the appropriate place in the code. The right order
   * of insert/collapse-calls defines the record-hierarchy.
   * @param s Record for symbolic execution primitive.
   * @return Identifier of the inserted record, must be given as argument to the
   *         respective call of collapse.
   */
  def insert(s: SymbolicRecord): Int = {

    if(!isUsed(s.value) || isRecordedDifferently(s))
      return -1

    current().subs = current().subs++List(s)
    stack = s::stack

    SEP_counter = SEP_counter+1
    SEP_set = SEP_set+SEP_counter
    return SEP_counter
  }

  /**
   * 'Finishes' the recording at the current node and goes one level higher in the record tree.
   * There should be only one call of collapse per insert.
   * @param v The node that will be 'collapsed'. Is only used for filtering-purposes, can be null.
   * @param n The identifier of the node (can NOT be null). The identifier is created by insert (return
   *          value).
   */
  def collapse(v: silver.ast.Node, n: Int): Unit =
  {
    if(n != -1 && SEP_set.contains(n)) {
      SEP_set = SEP_set - n
      if (isUsed(v))
        stack = stack.tail
    }
  }

  private def isRecordedDifferently(s: SymbolicRecord): Boolean =
  {
    s.value match {
      case v: silver.ast.MethodCall =>
        s match {
          case _: MethodCallRecord => false
          case _ => true
        }
      case v: silver.ast.CondExp =>
        s match {
          case _: EvaluateRecord => true
          case _ => false
        }

      case _ => false
    }
  }

  private def isUsed(node: silver.ast.Node): Boolean =
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
          /*case _: ast.CondExp /*| _: ast.TrueLit | _: ast.FalseLit | _: ast.NullLit | _: ast.IntLit | _: ast.FullPerm | _: ast.NoPerm
               | _: ast.AbstractLocalVar | _: ast.WildcardPerm | _: ast.FractionalPerm | _: ast.Result
               | _: ast.WildcardPerm | _: ast.FieldAccess */=>
            return false*/
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

  /**
   * Creates a DOT-representation of the record. Contains ONLY the creation and linking of nodes,
   * does NOT contain the necessary initialization for GraphViz (eg., digraph {...}). For output that can
   * be directly used by GraphViz, have a look at SymbExLogger.writeDotFile().
   * @return Returns the part of a DOT-graph that represents the record.
   */
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

  def toJSTree():String = {
    var output = ""
    output = output + recordToJS(main) + "\n"
    return output
  }

  private def recordToJS(s: SymbolicRecord):String = {
    var output = ""
    s match {
      case ite: IfThenElseRecord => {
        output = output + "{ name: \'IfThenElse\', open: true, prestate: "
        output = output + "{store: \"\", heap: \"\", pcs: \"\"}"
        output = output + "\n, children: [\n"
        output = output + "{ name: \'if " +ite.thnCond.toSimpleString()+ "\', open: true, prestate: "
        output = output + "{store: \"\", heap: \"\", pcs: \"\"}"
        output = output + ",\n children: [\n"
        for (sub <- ite.thnSubs) {
          output = output + recordToJS(sub) + ", \n"
        }
        output = output + "]},\n"
        output = output + "{ name: \'else " +ite.elsCond.toSimpleString()+ "\', open: true, prestate: "
        output = output + "{store: \"\", heap: \"\", pcs: \"\"}"
        output = output + ",\n children: [\n"
        for (sub <- ite.elsSubs) {
          output = output + recordToJS(sub) + ", \n"}
        output = output + "]}\n"
        output = output + "]}"
      }
      case ce: CondExpRecord => {
        output = output + "{ name: \'"+ce.toString()+"\', open: true, prestate: "
        output = output + "{store: \"\", heap: \"\", pcs: \"\"}"
        output = output + "\n, children: [\n"
        output = output + recordToJS(ce.thnExp) + ", \n"
        output = output + recordToJS(ce.elsExp) + "]}"
      }
      case mc: MethodCallRecord => {
        output = output + "{ name: \'"+mc.toString()+"\', open: true, prestate: "
        output = output + "{store: \"\", heap: \"\", pcs: \"\"}"
        output = output + "\n, children: [\n"

        output = output + "{ name: \'parameters\', open: true, prestate: "
        output = output + "{store: \"\", heap: \"\", pcs: \"\"}"
        output = output + "\n, children: [\n"
        for(p <- mc.parameters){
          output = output + recordToJS(p) + ", \n"
        }
        output = output + "]},"

        output = output + "{ name: \'precondition\', open: true, prestate: "
        output = output + "{store: \"\", heap: \"\", pcs: \"\"}"
        output = output + "\n, children: [\n"
        output = output + recordToJS(mc.precondition)
        output = output + "]},"

        output = output + "{ name: \'postcondition\', open: true, prestate: "
        output = output + "{store: \"\", heap: \"\", pcs: \"\"}"
        output = output + "\n, children: [\n"
        output = output + recordToJS(mc.postcondition)
        output = output + "]}"

        output = output + "]}"
      }
      case cr: CommentRecord => {
        output = output + "{ name: \'"+cr.toString+"\', open: true, prestate: "
        output = output + "{store: \"\", heap: \"\", pcs: \"\"}}"
      }
      case _ => {
        output = output + "{ name: \'" + s.toString() + "\', open: true, prestate: "
        output = output + "{store: \"\", heap: \"\", pcs: \"\"}"
        if (!s.subs.isEmpty) {
          output = output + ",\n children: [\n"
          for (sub <- s.subs) {
            output = output + recordToJS(sub) + ", \n"
          }
          output = output + "]"
        }
        output = output + "}"
      }
    }
    return output
  }


}

//=========================

trait SymbolicRecord {
  val value: silver.ast.Node
  val state: AnyRef
  val context: DefaultContext
  var subs = List[SymbolicRecord]()

  override def toString():String = {
    toTypeString() + " " + toSimpleString()
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

  def toTypeTree(n: Int):String = {
    var ident = ""
    for(i <- 1 to n) {
      ident = "  " + ident
    }
    var str:String = toTypeString()+"\n"
    for(s <- subs){
      str = str + ident + s.toTypeTree(n+1)
    }
    str
  }

  def toTypeString():String {}

  def dotNode(): String = {
    this.hashCode().toString()
  }

  def dotLabel(): String = {
    "\""+this.toString()+"\""
  }
}

trait MemberRecord extends SymbolicRecord
trait MultiChildRecord extends SymbolicRecord
trait MultiChildOrderedRecord extends MultiChildRecord
trait MultiChildUnorderedRecord extends MultiChildRecord
trait SequentialRecord extends SymbolicRecord

class MethodRecord(v: silver.ast.Method, s: AnyRef, c: DefaultContext) extends MemberRecord {
  val value = v
  val state = s
  val context = c

  override def toSimpleString():String = {
    if(value != null) value.name
    else "null"
  }

  def toTypeString():String = { "method" }
}

class PredicateRecord(v: silver.ast.Predicate, s: AnyRef, c: DefaultContext) extends MemberRecord {
  val value = v
  val state = s
  val context = c

  override def toSimpleString():String = {
    if(value != null) value.name
    else "null"
  }

  def toTypeString():String = { "predicate" }
}

class FunctionRecord(v: silver.ast.Function, s: AnyRef, c: DefaultContext) extends MemberRecord {
  val value = v
  val state = s
  val context = c

  override def toSimpleString():String = {
    if(value != null) value.name
    else "null"
  }

  def toTypeString():String = { "function" }
}

class ExecuteRecord(v: silver.ast.Stmt, s: AnyRef, c: DefaultContext) extends SequentialRecord {
  val value = v
  val state = s
  val context = c
  def toTypeString():String = { "execute" }
}

class EvaluateRecord(v: silver.ast.Exp, s: AnyRef, c: DefaultContext) extends SequentialRecord {
  val value = v
  val state = s
  val context = c
  def toTypeString():String = { "evaluate" }
}

class ProduceRecord(v: silver.ast.Exp, s: AnyRef, c: DefaultContext) extends SequentialRecord {
  val value = v
  val state = s
  val context = c
  def toTypeString():String = { "produce" }
}

class ConsumeRecord(v: silver.ast.Exp, s: AnyRef, c: DefaultContext) extends SequentialRecord {
  val value = v
  val state = s
  val context = c
  def toTypeString():String = { "consume" }
}

class IfThenElseRecord(v: silver.ast.Exp, s: AnyRef, c: DefaultContext) extends MultiChildUnorderedRecord {
  val value = v //meaningless since there is no directly usable if-then-else structure in the AST
  val state = s
  val context = c
  def toTypeString():String = { "IfThenElse" }

  var thnCond:SymbolicRecord = new CommentRecord("Unreachable", null, null)
  var elsCond:SymbolicRecord = new CommentRecord("Unreachable", null, null)
  var thnSubs = List[SymbolicRecord](new CommentRecord("Unreachable", null, null))
  var elsSubs = List[SymbolicRecord](new CommentRecord("Unreachable", null, null))

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
    str = str + "if " + thnCond.toSimpleString()+"\n"
    str = str + ident + thnCond.toSimpleTree(n+1)
    for(s <- thnSubs){
      str = str + ident + s.toSimpleTree(n+1)
    }

    str = str + ident.substring(2) + "else " + elsCond.toSimpleString()+"\n"
    str = str + ident + elsCond.toSimpleTree(n+1)
    for(s <- elsSubs){
      str = str + ident + s.toSimpleTree(n+1)
    }
    return str
  }

  override def toTypeTree(n: Int): String ={
    var ident = ""
    for(i <- 1 to n) {
      ident = "  " + ident
    }

    var str = ""
    str = str + "if\n"
    str = str + ident + thnCond.toTypeTree(n+1)
    for(s <- thnSubs){
      str = str + ident + s.toTypeTree(n+1)
    }

    str = str + ident.substring(2) + "else\n"
    str = str + ident + elsCond.toTypeTree(n+1)
    for(s <- elsSubs){
      str = str + ident + s.toTypeTree(n+1)
    }
    return str
  }

  def finish_thnCond(): Unit ={
    if(!subs.isEmpty)
      thnCond = subs(0)
    subs = List[SymbolicRecord]()
  }

  def finish_elsCond(): Unit ={
    if(!subs.isEmpty)
      elsCond = subs(0)
    subs = List[SymbolicRecord]()
  }

  def finish_thnSubs(): Unit ={
    if(!subs.isEmpty)
      thnSubs = subs
    subs = List[SymbolicRecord]()
  }

  def finish_elsSubs(): Unit ={
    if(!subs.isEmpty)
      elsSubs = subs
    subs = List[SymbolicRecord]()
  }
}

class CondExpRecord(v: silver.ast.Exp, s: AnyRef, c: DefaultContext) extends MultiChildOrderedRecord {
  val value = v
  val state = s
  val context = c
  def toTypeString():String = { "CondExp" }

  var cond:SymbolicRecord   = new EvaluateRecord(null, null, null)
  // thn/els Exp is Unreachable by default. If this is not the case, it will be overwritten
  var thnExp:SymbolicRecord = new CommentRecord("Unreachable", null, null)
  var elsExp:SymbolicRecord = new CommentRecord("Unreachable", null, null)

  override def toString(): String = {
    if(v != null)
      "evaluate: "+v.toString()
    else
      "CondExp <null>"
  }

  override def toSimpleString(): String = {
    if(v != null)
      v.toString()
    else
      "CondExp <Null>"
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

  override def toTypeTree(n: Int):String = {
    var ident = ""
    for(i <- 1 to n) {
      ident = "  " + ident
    }
    var str = ""
    str = str + "CondExp\n"
    str = str + ident + thnExp.toTypeTree(n+1)
    str = str + ident + elsExp.toTypeTree(n+1)
    return str
  }

  def finish_cond(): Unit ={
    if(!subs.isEmpty)
      cond = subs(0)
    subs = List[SymbolicRecord]()
  }

  def finish_thnExp(): Unit ={
    if(!subs.isEmpty)
      thnExp = subs(0)
    subs = List[SymbolicRecord]()
  }

  def finish_elsExp(): Unit ={
    if(!subs.isEmpty)
      elsExp = subs(0)
    subs = List[SymbolicRecord]()
  }
}

class CommentRecord(str: String, s: AnyRef, c: DefaultContext) extends SequentialRecord {
  val value = null
  val state = s
  val context = c
  def toTypeString():String = { "Comment" }

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

class MethodCallRecord(v: silver.ast.MethodCall, s: AnyRef, c: DefaultContext) extends MultiChildOrderedRecord {
  val value = v
  val state = s
  val context = c
  def toTypeString():String = { "MethodCall" }

  var parameters = List[SymbolicRecord]()
  var precondition: SymbolicRecord = new ConsumeRecord(null,null, null)
  var postcondition:SymbolicRecord = new ProduceRecord(null,null, null)

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

  override def toTypeTree(n: Int):String = {
    var ident = ""
    for(i <- 1 to n) {
      ident = "  " + ident
    }
    var str = ""
    str = str + "MethodCall\n"
    str = str + ident + "precondition\n"
    str = str + ident + "  " + precondition.toTypeTree(n+2)
    str = str + ident + "postcondition\n"
    str = str + ident + "  " + postcondition.toTypeTree(n+2)
    for(p <- parameters) {
      str = str + ident + "parameter\n"
      str = str + ident + "  " + p.toTypeTree(n+2)
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

  def finish_parameters(): Unit ={
    parameters = subs
    subs = List[SymbolicRecord]()
  }

  def finish_precondition(): Unit ={
    precondition = subs(0)
    subs = List[SymbolicRecord]()
  }

  def finish_postcondition(): Unit ={
    postcondition = subs(0)
    subs = List[SymbolicRecord]()
  }
}


/**
 * ================================
 * GUIDE FOR EXTENDING SymbExLogger
 * ================================
 *
 * SymbExLogger records all calls of the four symbolic primitives Execute, Evaluate, Produce
 * and Consume. By default, only the current state and parameters of the primitives are stored.
 * If you want to get more information from certain structures, there are several ways to store additional
 * info:
 *
 * 1) Store the information as a CommentRecord.
 * 2) Implement a customized record.
 *
 * Use of CommentRecord (1):
 *    At the point in the code where you want to add the comment, call
 *    //SymbExLogger.currentLog().insert(new CommentRecord(my_info, σ, c)
 *    //SymbExLogger.currentLog().collapse()
 *    σ is the current state (AnyRef, but should be of type State[_,_,_] usually), my_info
 *    is a string that contains the information you want to store, c is the current
 *    context. If you want to store more information than just a string, consider (2).
 *
 * Use of custom Records (2):
 *    For already existing examples, have a look at CondExpRecord (local Branching) or IfThenElseRecord
 *    (recording of If-Then-Else-structures).
 *    Assume that you want to have a custom record for  (non-short-circuiting) evaluations of
 *    silver.ast.And, since you want to differ between the evaluation of the lefthandside
 *    and the righthandside (not possible with default recording).
 *    Your custom record could look similar to this:
 *
 *    class AndRecord(v: silver.ast.And, s: AnyRef, c: DefaultContext) extends SymbolicRecord {
 *      val value = v    // Due to inheritance. This is what gets recorded by default.
 *      val state = s    // "
 *      val context = c  // "
 *
 *      lhs: SymbolicRecord = new CommentRecord("null", null, null)
 *      rhs: SymbolicRecord = new CommentRecord("null", null, null)
 *      // lhs & rhs are what you're interested in. The first initialization should be overwritten anyway,
 *      // initialization with a CommentRecord just ensures that the logger won't crash due
 *      // to a Null Exception (ideally).
 *
 *      def finish_lhs(): Unit ={
 *        lhs = subs(0)
 *        subs = List[SymbolicRecord]()
 *      }
 *
 *      def finish_rhs(): Unit = {
 *        rhs = subs(0)
 *        subs = List[SymbolicRecord]()
 *      }
 *
 *      override def toSimpleTree:String = {..} // See below or have a look at existing examples
 *
 *      // finish_FIELD() is the method that overwrites the given field with what is currently in 'subs'.
 *      // For usage example, see below.
 *    }
 *
 *    Usage of your new custom record 'AndRecord':
 *    This is the code in the DefaultEvaluator (after unrolling of evalBinOp):
 *
 *    case ast.And(e0, e1) if config.disableShortCircuitingEvaluations() =>
 *      eval(σ, e0, pve, c)((t0, c1) =>
 *        eval(σ, e1, pve, c1)((t1, c2) =>
 *          Q(And(t0, t1), c2)))
 *
 *    Use of the new record:
 *
 *    case and @ ast.And(e0, e1) if config.disableShortCircuitingEvaluations() =>
 *      andRec = new AndRecord(and, σ, c)
 *      SymbExLogger.currentLog().insert(andRec)
 *      eval(σ, e0, pve, c)((t0, c1) => {
 *        andRec.finish_lhs()
 *        eval(σ, e1, pve, c1)((t1, c2) => {
 *          andRec.finish_rhs()
 *          SymbExLogger.currentLog().collapse()
 *          Q(And(t0, t1), c2)))}}
 *
 *    The record is now available for use; now its representation needs to be implemented.
 *    For the 'simpleTree'-output, override the 'toSimpleTree()'-method in AndRecord.
 *    For the DOT-output, implement a case-distinction for AndRecord (see method subsToDot
 *    in the SymbLog-class):
 *    For every field in your record (here: lhs & rhs), add a line that creates a node, and connect
 *    those to the previousNode (see subsToDot() for examples). Make use of the dotLabel() and
 *    dotNode() method that are inherited from SymbolicRecord (in some cases, you might need to
 *    override them).
 *    To avoid 'double recording' (i.e., disable default recording during recording on custom records),
 *    add AndRecord to 'isRecordedDifferently()' in SymbLog (same fashion as existing records).
 *    Otherwise, Evaluations of 'Ands' will appear twice in the logging tree.
 */

