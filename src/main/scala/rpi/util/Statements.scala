package rpi.util

import viper.silver.ast

object Statements {
  @inline
  def makeSkip: ast.Seqn =
    makeSequence(Seq.empty)

  def makeSequence(statement: ast.Stmt): ast.Seqn =
    statement match {
      case sequence: ast.Seqn => sequence
      case other => makeSequence(Seq(other))
    }

  @inline
  def makeSequence(statements: Seq[ast.Stmt], declarations: Seq[ast.Declaration] = Seq.empty): ast.Seqn =
    ast.Seqn(statements, declarations)()

  @inline
  def makeConditional(condition: ast.Exp, thenBranch: ast.Stmt, elseBranch: ast.Stmt): ast.If =
    ast.If(condition, makeSequence(thenBranch), makeSequence(elseBranch))()

  @inline
  def makeLoop(condition: ast.Exp, body: ast.Stmt, invariants: Seq[ast.Exp] = Seq.empty): ast.While =
    ast.While(condition, invariants, makeSequence(body))()

  @inline
  def makeAssign(target: ast.LocalVar, value: ast.Exp): ast.LocalVarAssign =
    ast.LocalVarAssign(target, value)()
}
