// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2025 ETH Zurich.

package viper.silicon.debugger

import viper.silver.ast

import java.nio.file.{Path, Paths}
import scala.util.Try

/** The position of a statement at which the verification can be paused. Lines and columns are 1-based. */
case class StatementLocation(file: String, line: Int, column: Int)

object StatementLocation {
  /** Normalizes a path so that a path sent by an IDE and one from a Viper position can be compared. */
  def normalize(file: String): String = Try(normalize(Paths.get(file))).getOrElse(file)

  def normalize(file: Path): String = {
    val s = file.toAbsolutePath.normalize.toString
    if (System.getProperty("os.name", "").toLowerCase.startsWith("windows")) s.toLowerCase else s
  }

  def of(stmt: ast.Stmt): Option[StatementLocation] = stmt.pos match {
    case sp: ast.AbstractSourcePosition =>
      Some(StatementLocation(normalize(sp.file), sp.start.line, sp.start.column))
    case _ => None
  }
}

/**
  * Maps the lines on which a user set breakpoints to statements of a program.
  *
  * Only statements that Silicon executes one by one (see [[viper.silicon.rules.executor]]) can be stopped at:
  * sequences, conditionals and loops are turned into control flow and are never executed as statements. A
  * breakpoint on a line without such a statement moves to the next line that has one, within the same method.
  */
class BreakpointResolver(program: ast.Program) {

  private case class Member(file: String, startLine: Int, endLine: Int, statements: Seq[StatementLocation])

  private val members: Seq[Member] = program.methods.flatMap { m =>
    (m.pos, m.body) match {
      case (sp: ast.AbstractSourcePosition, Some(body)) =>
        val statements = body.deepCollect {
          case s: ast.Stmt if BreakpointResolver.isExecuted(s) => StatementLocation.of(s)
        }.flatten.distinct.sortBy(l => (l.line, l.column))
        Some(Member(StatementLocation.normalize(sp.file), sp.start.line, sp.end.getOrElse(sp.start).line, statements))
      case _ => None
    }
  }

  /** The number of `package` proof scripts each statement is nested in. */
  private val depths: Map[StatementLocation, Int] = {
    def visit(n: ast.Node, depth: Int): Seq[(StatementLocation, Int)] = {
      val here = n match {
        case s: ast.Stmt if BreakpointResolver.isExecuted(s) => StatementLocation.of(s).map(_ -> depth).toSeq
        case _ => Seq.empty
      }
      val inner = n match {
        case p: ast.Package => p.proofScript.ss.flatMap(visit(_, depth + 1))
        case other => other.subnodes.flatMap(visit(_, depth))
      }
      here ++ inner
    }
    program.methods.flatMap(_.body.toSeq.flatMap(visit(_, 0))).toMap
  }

  /** How many `package` proof scripts the statement at `location` is nested in; 0 if it is in none. */
  def depth(location: StatementLocation): Int = depths.getOrElse(location, 0)

  /** The statement at which a breakpoint on `line` of `file` stops, if any. */
  def resolve(file: String, line: Int): Option[StatementLocation] = {
    val normalized = StatementLocation.normalize(file)
    members.find(m => m.file == normalized && m.startLine <= line && line <= m.endLine)
      .flatMap(_.statements.find(_.line >= line))
  }
}

object BreakpointResolver {
  def isExecuted(stmt: ast.Stmt): Boolean = stmt match {
    case _: ast.Seqn | _: ast.If | _: ast.While | _: ast.Goto => false
    case _ => true
  }
}
