// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package rpi.util.ast

import rpi.inference.annotation.{Annotation, Hint}
import rpi.inference.context.Check
import rpi.util.ast.Expressions._
import rpi.util.ast.Statements._
import viper.silver.ast
import viper.silver.ast.pretty.FastPrettyPrinter._
import viper.silver.ast.pretty.PrettyPrintPrimitives

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

  @inline
  def makeInhale(expression: ast.Exp, info: ast.Info = ast.NoInfo): ast.Inhale =
    ast.Inhale(expression)(info = info)

  @inline
  def makeExhale(expression: ast.Exp, info: ast.Info = ast.NoInfo): ast.Exhale =
    ast.Exhale(expression)(info = info)

  @inline
  def makeLabel(name: String): ast.Label =
    ast.Label(name, Seq.empty)()

  def makeHinted(body: ast.Seqn, hints: Seq[Hint]): Hinted =
    Hinted(body, hints)()

  @inline
  def makeCut(statement: ast.Stmt, check: Check): Cut =
    Cut(statement)(info = ValueInfo(check))
}

case class Hinted(body: ast.Seqn, hints: Seq[Hint])
                 (override val pos: ast.Position = ast.NoPosition,
                  override val info: ast.Info = ast.NoInfo,
                  override val errT: ast.ErrorTrafo = ast.NoTrafos) extends ast.ExtensionStmt {
  override def extensionSubnodes: Seq[ast.Node] =
    Seq(body)

  override def prettyPrint: PrettyPrintPrimitives#Cont =
    text("hinted") <+> showBlock(body)
}

case class Cut(statement: ast.Stmt)
              (override val pos: ast.Position = ast.NoPosition,
               override val info: ast.Info = ast.NoInfo,
               override val errT: ast.ErrorTrafo = ast.NoTrafos) extends ast.ExtensionStmt {

  lazy val havocked: Seq[ast.LocalVar] =
    statement match {
      case call: ast.MethodCall => call.targets
      case loop: ast.While => loop.writtenVars
      case _ => sys.error(s"Unexpected cut: $statement")
    }

  lazy val havoc: ast.Stmt = {
    val assignments = havocked.map { variable => makeAssign(variable, variable) }
    makeLoop(makeFalse, makeSequence(assignments))
  }

  override def extensionSubnodes: Seq[ast.Node] =
    Seq.empty

  override def prettyPrint: PrettyPrintPrimitives#Cont =
    text(s"havoc(${havocked.mkString(", ")})")
}