package rpi.context

import rpi.Names
import rpi.util.Statements._
import viper.silver.ast

/**
  * An annotation.
  *
  * @param name     The name.
  * @param argument The argument.
  */
case class Annotation(name: String, argument: ast.Exp) {
  override def toString: String = s"$name($argument)"
}

object Annotations {

  def extract(sequence: ast.Seqn): (Seq[Annotation], ast.Seqn) = {
    val (annotations, statements) = extract(sequence.ss)
    val updated = makeSequence(statements, sequence.scopedDecls)
    (annotations, updated)
  }

  def extract(statements: Seq[ast.Stmt]): (Seq[Annotation], Seq[ast.Stmt]) =
    statements match {
      case rest :+ ast.MethodCall(name, Seq(argument), _) if Names.isAnnotation(name) =>
        val (suffix, trimmed) = trimAnnotations(rest)
        val annotation = Annotation(name, argument)
        (suffix :+ annotation, trimmed)
      case _ => (Seq.empty, statements)
    }

  @deprecated
  def trimAnnotations(statements: Seq[ast.Stmt]): (Seq[Annotation], Seq[ast.Stmt]) = ???
}