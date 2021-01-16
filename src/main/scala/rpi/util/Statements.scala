package rpi.util

import viper.silver.ast

object Statements {

  import Expressions._

  @inline
  def skip: ast.Seqn =
    asSequence(Seq.empty)

  def asSequence(statement: ast.Stmt): ast.Seqn =
    statement match {
      case sequence: ast.Seqn => sequence
      case other => ast.Seqn(Seq(other), Seq.empty)()
    }

  @inline
  def asSequence(statements: Seq[ast.Stmt]): ast.Seqn =
    ast.Seqn(statements, Seq.empty)()

  @inline
  def conditional(conditions: Seq[ast.Exp], body: ast.Stmt): ast.Stmt =
    conditional(conditions, body, skip)

  def conditional(conditions: Seq[ast.Exp], thenBody: ast.Stmt, elseBody: ast.Stmt): ast.Stmt =
    if (conditions.isEmpty) thenBody
    else ast.If(bigAnd(conditions), asSequence(thenBody), asSequence(elseBody))()
}
