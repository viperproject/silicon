package rpi.util

import viper.silver.ast

object Statements {
  def skip: ast.Seqn =
    asSequence(Seq.empty)

  def asSequence(statement: ast.Stmt): ast.Seqn =
    statement match {
      case sequence: ast.Seqn => sequence
      case other => ast.Seqn(Seq(other), Seq.empty)()
    }

  def asSequence(statements: Seq[ast.Stmt]): ast.Seqn =
    ast.Seqn(statements, Seq.empty)()
}
