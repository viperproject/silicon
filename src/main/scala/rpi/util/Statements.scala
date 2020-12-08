package rpi.util

import viper.silver.{ast => sil}

object Statements {
  def skip: sil.Seqn =
    asSequence(Seq.empty)

  def asSequence(statement: sil.Stmt): sil.Seqn =
    statement match {
      case sequence: sil.Seqn => sequence
      case other => sil.Seqn(Seq(other), Seq.empty)()
    }

  def asSequence(statements: Seq[sil.Stmt]): sil.Seqn =
    sil.Seqn(statements, Seq.empty)()
}
