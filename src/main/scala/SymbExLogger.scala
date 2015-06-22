/**
 * Created by admin on 20.06.2015.
 */

package viper
package silicon

import silver.ast
import interfaces.state.factoryUtils.Ø
import interfaces.state.{StateFactory, HeapFactory, Store}
import viper.silver.ast.Node

object SymbExLogger {
  var mpf_list = List[SymbLog]()

  def insert(mpf: silver.ast.Node, s: AnyRef): Unit ={
    // mpf: Method, Predicate or Function
    mpf_list = mpf_list ++ List(new SymbLog(mpf,s))
  }

  def currentLog(): SymbLog = {
    mpf_list.last
  }
}


class SymbLog(v: silver.ast.Node, s: AnyRef) {
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

    if(!isUsed(s.value))
      return -1

    /*if(flag_comment_stack) {
      sr = new SymbRec(ptype, v, comment_stack.head, branchlevel, s)
      comment_stack = comment_stack.tail
      flag_comment_stack = false
    }
    else {
      sr = new SymbRec(ptype, v, branchlevel, s)
    }
    debug_println(sr.toString())
    current().subs = current().subs++List(sr)
    stack = sr::stack


    SEP_counter = SEP_counter+1
    SEP_set = SEP_set+SEP_counter

    if(flag_manual_collapse) {
      manual_collapse_set = manual_collapse_set + SEP_counter
      flag_manual_collapse = false
    }*/

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
    if(SEP_set.contains(n)) {
      SEP_set = SEP_set - n
      if (isUsed(v))
        stack = stack.tail
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
          case _: ast.TrueLit | _: ast.FalseLit | _: ast.NullLit | _: ast.IntLit | _: ast.FullPerm | _: ast.NoPerm
               | /*_: ast.AbstractLocalVar |*/ _: ast.WildcardPerm | _: ast.FractionalPerm | _: ast.Result
               | _: ast.WildcardPerm | _: ast.FieldAccess =>
            return false
          case _ =>
            return true
        }
      }
      case _ => return true
    }
  }
}

//=========================

trait SymbolicRecord {
  val value: silver.ast.Node
  val state: AnyRef
  var subs = List[SymbolicRecord]()

  override def toString():String = {
    value.toString()
  }

  def toSimpleTree(n: Int):String = {
    var ident = ""
    for(i <- 1 to n)
      ident = ident + " "
    var str:String = ident + this.toString()+"\n"
    for(s <- subs){
      str = str + ident + " " + s.toSimpleTree(n+1)
    }
    str
  }
}

class MethodRecord(v: silver.ast.Method, s: AnyRef) extends SymbolicRecord {
  val value = v
  val state = s

  override def toString():String = {
    "method "+value.name
  }
}

class PredicateRecord(v: silver.ast.Predicate, s: AnyRef) extends SymbolicRecord {
  val value = v
  val state = s

  override def toString():String = {
    "predicate "+value.name
  }
}

class FunctionRecord(v: silver.ast.Function, s: AnyRef) extends SymbolicRecord {
  val value = v
  val state = s

  override def toString():String = {
    "function "+value.name
  }
}

class ExecuteRecord(v: silver.ast.Stmt, s: AnyRef) extends SymbolicRecord {
  val value = v
  val state = s

  override def toString():String = {
    "execute: "+value.toString()
  }
}

class EvaluateRecord(v: silver.ast.Exp, s: AnyRef) extends SymbolicRecord {
  val value = v
  val state = s

  override def toString():String = {
    "evaluate: "+value.toString()
  }
}

class ProduceRecord(v: silver.ast.Exp, s: AnyRef) extends SymbolicRecord {
  val value = v
  val state = s

  override def toString():String = {
    "produce: "+value.toString()
  }
}

class ConsumeRecord(v: silver.ast.Exp, s: AnyRef) extends SymbolicRecord {
  val value = v
  val state = s

  override def toString():String = {
    "execute: "+value.toString()
  }
}