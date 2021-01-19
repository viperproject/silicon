package rpi.util

import viper.silver.ast

object Statements {

  import Expressions._

  @inline
  def makeSkip: ast.Seqn =
    makeSequence(Seq.empty)

  def makeSequence(statement: ast.Stmt): ast.Seqn =
    statement match {
      case sequence: ast.Seqn => sequence
      case other => ast.Seqn(Seq(other), Seq.empty)()
    }

  @inline
  def makeSequence(statements: Seq[ast.Stmt]): ast.Seqn =
    ast.Seqn(statements, Seq.empty)()

  @inline
  def makeConditional(conditions: Seq[ast.Exp], body: ast.Stmt): ast.Stmt =
    makeConditional(conditions, body, makeSkip)

  @inline
  def makeConditional(conditions: Seq[ast.Exp], thenBody: ast.Stmt, elseBody: ast.Stmt): ast.Stmt =
    if (conditions.isEmpty) thenBody
    else makeConditional(makeAnd(conditions), thenBody, elseBody)

  @inline
  def makeConditional(condition: ast.Exp, thenBody: ast.Stmt, elseBody: ast.Stmt): ast.If =
    ast.If(condition, makeSequence(thenBody), makeSequence(elseBody))()
}
