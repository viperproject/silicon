// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.supporters.functions

import viper.silver.ast
import viper.silicon.common.Mergeable
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.rules.{InverseFunctions, SnapshotMapDefinition}
import viper.silicon.{Map, Stack}
import viper.silicon.state.terms._

// TODO: FunctionRecorder records Function, Var, etc., which are later on turned into corresponding
//       declarations (e.g. FunctionDecl), see FunctionData's field freshSymbolsAcrossAllPhases.
//       Only macros are already recorded as MacroDecls — this should be the case for Functions,
//       etc. as well.
trait FunctionRecorder extends Mergeable[FunctionRecorder] {
  def data: Option[FunctionData]
  private[functions] def locToSnaps: Map[ast.LocationAccess, InsertionOrderedSet[(Stack[Term], Term)]]
  def locToSnap: Map[ast.LocationAccess, Term]
  private[functions] def fappToSnaps: Map[ast.FuncApp, InsertionOrderedSet[(Stack[Term], Term)]]
  def fappToSnap: Map[ast.FuncApp, Term]
  def freshFvfsAndDomains: InsertionOrderedSet[SnapshotMapDefinition]
  def freshFieldInvs: InsertionOrderedSet[InverseFunctions]
  def freshConstrainedVars: InsertionOrderedSet[(Var, Term)]
  def freshConstraints: InsertionOrderedSet[Term]
  def freshSnapshots: InsertionOrderedSet[Function]
  def freshPathSymbols: InsertionOrderedSet[Function]
  def freshMacros: InsertionOrderedSet[MacroDecl]
  def recordSnapshot(loc: ast.LocationAccess, guards: Stack[Term], snap: Term): FunctionRecorder
  def recordSnapshot(fapp: ast.FuncApp, guards: Stack[Term], snap: Term): FunctionRecorder
  def recordFvfAndDomain(fvfDef: SnapshotMapDefinition): FunctionRecorder
  def recordFieldInv(inv: InverseFunctions): FunctionRecorder
  def recordConstrainedVar(v: Var, constraint: Term): FunctionRecorder
  def recordConstraint(constraint: Term): FunctionRecorder
  def recordFreshSnapshot(snap: Function): FunctionRecorder
  def recordPathSymbol(symbol: Function): FunctionRecorder
  def recordFreshMacro(decl: MacroDecl): FunctionRecorder
  def depth: Int
  def changeDepthBy(delta: Int): FunctionRecorder
}

case class ActualFunctionRecorder(private val _data: FunctionData,
                                  private[functions] val locToSnaps: Map[ast.LocationAccess, InsertionOrderedSet[(Stack[Term], Term)]] = Map(),
                                  private[functions] val fappToSnaps: Map[ast.FuncApp, InsertionOrderedSet[(Stack[Term], Term)]] = Map(),
                                  freshFvfsAndDomains: InsertionOrderedSet[SnapshotMapDefinition] = InsertionOrderedSet(),
                                  freshFieldInvs: InsertionOrderedSet[InverseFunctions] = InsertionOrderedSet(),
                                  freshConstrainedVars: InsertionOrderedSet[(Var, Term)] = InsertionOrderedSet(),
                                  freshConstraints: InsertionOrderedSet[Term] = InsertionOrderedSet(),
                                  freshSnapshots: InsertionOrderedSet[Function] = InsertionOrderedSet(),
                                  freshPathSymbols: InsertionOrderedSet[Function] = InsertionOrderedSet(),
                                  freshMacros: InsertionOrderedSet[MacroDecl] = InsertionOrderedSet(),
                                  depth: Int = 0)
    extends FunctionRecorder {

  /* Depth is intended to reflect how often a nested function application or unfolding expression
   * has been entered, where entered means, that a function application's precondition is consumed
   * or that an unfolded preciate's body is produced (and similar for applying a magic wand).
   * On depth 0, mappings from heap-dependent expressions to snapshots need to be recorded, but not
   * on higher levels, since expressions encountered do not (directly) occur in the function for
   * whose axiomatisation we currently record information.
   * On depths 0 and 1, newly declared symbols, e.g. summarising snapshot maps, need to be recorded
   * because both may occur in the snapshots to which heap-dependent expressions are mapped. Symbols
   * declared on higher depths, however cannot occur in these snapshots, and therefore don't need to
   * be recorded.
   *
   * Consider the following members:
   *
   *   function f()
   *     ...
   *   { ... unfolding P() in g() ... }
   *
   *   function g()
   *     ...
   *     requires ... unfolding Q() in h() ...
   *
   *   predicate P()
   *   { ... unfolding Q() in h() ... }
   *
   * When recording data for axiomatising f(), the production of P's body happens on depth 1, as
   * does the consumption of g's precondition, whereas the same happens for Q and g on depth 2.
   * A snapshot introduced by P/g may occur in any snapshot to which heap-dependent expressions
   * from f's body (or contract) are mapped.
   * However, any snapshot introduced by Q/h cannot occur in a snapshot that is used to axiomatise
   * f: for h, that is because these function applications are not part of f; for Q, that is because
   * snapshots introduced by unfolding Q can only occur in heap-dependent expressions from the
   * unfolding's in-clause, which, as argued before, are not part of f.
   */

  val data = Some(_data)

  private def exprToSnap[E <: ast.Exp]
                        (recordings: Map[E, InsertionOrderedSet[(Stack[Term], Term)]])
                        : Map[E, Term] = {

    recordings.map { case (expr, guardsToSnap) =>
      expr -> toTerm(guardsToSnap, None)
    }
  }

  private def toTerm(snaps: InsertionOrderedSet[(Stack[Term], Term)], alternative: Option[Term]): Term = {
    assert(snaps.nonEmpty)
    if (snaps.size == 1) {
      alternative match {
        case Some(alt) => Ite(And(snaps.head._1.toSet), snaps.head._2, alt)
        case None => snaps.head._2
      }
    } else {
      if (snaps.head._1.isEmpty) {
        snaps.head._2
      } else {
        val firstBranch = snaps.head._1.head
        val grouped = snaps.groupBy(sn => {
          if (sn._1.nonEmpty && sn._1.head == firstBranch)
            1 // starting with firstBranch
          else if (sn._1.nonEmpty && sn._1.head == Not(firstBranch))
            2 // starting with Not(firstBranch)
          else
            3 // starting with other condition
        })

        def dropFirst(part: InsertionOrderedSet[(Stack[Term], Term)]): InsertionOrderedSet[(Stack[Term], Term)] = {
          part.map(sn => (sn._1.tail, sn._2))
        }

        val newAlt = if (grouped.contains(3)) Some(toTerm(grouped(3), alternative)) else alternative
        if (grouped.contains(1) && grouped.contains(2)) {
          val left = toTerm(dropFirst(grouped(1)), newAlt)
          val right = toTerm(dropFirst(grouped(2)), newAlt)
          Ite(firstBranch, left, right)
        } else {
          if (grouped.contains(1)) {
            newAlt match {
              case Some(actAlt) => Ite(firstBranch, toTerm(dropFirst(grouped(1)), newAlt), actAlt)
              case None => toTerm(dropFirst(grouped(1)), newAlt)
            }
          } else {
            newAlt match {
              case Some(actAlt) => Ite(Not(firstBranch), toTerm(dropFirst(grouped(2)), newAlt), actAlt)
              case None => toTerm(dropFirst(grouped(2)), newAlt)
            }
          }
        }
      }
    }
  }

  def locToSnap: Map[ast.LocationAccess, Term] = exprToSnap(locToSnaps)
  def fappToSnap: Map[ast.FuncApp, Term] = exprToSnap(fappToSnaps)

  private def recordExpressionSnapshot[E <: ast.Exp]
                                      (loc: E,
                                       guards: Stack[Term],
                                       snap: Term,
                                       recordings: Map[E, InsertionOrderedSet[(Stack[Term], Term)]])
                                      : Option[Map[E, InsertionOrderedSet[(Stack[Term], Term)]]] = {

    if (depth == 0) {
      val guardsToSnaps = recordings.getOrElse(loc, InsertionOrderedSet()) + (guards -> snap)

      Some(recordings + (loc -> guardsToSnaps))
    } else {
      None
    }
  }

  def recordSnapshot(loc: ast.LocationAccess, guards: Stack[Term], snap: Term)
                    : ActualFunctionRecorder = {

    recordExpressionSnapshot(loc, guards, snap, locToSnaps)
      .fold(this)(updatedLocToSnaps => copy(locToSnaps = updatedLocToSnaps))
  }

  def recordSnapshot(fapp: ast.FuncApp, guards: Stack[Term], snap: Term)
                    : ActualFunctionRecorder = {

    recordExpressionSnapshot(fapp, guards, snap, fappToSnaps)
      .fold(this)(updatedFAppToSnaps => copy(fappToSnaps = updatedFAppToSnaps))
  }

  def recordFvfAndDomain(fvfDef: SnapshotMapDefinition): ActualFunctionRecorder =
    if (depth <= 2) copy(freshFvfsAndDomains = freshFvfsAndDomains + fvfDef)
    else this

  def recordFieldInv(inv: InverseFunctions): ActualFunctionRecorder =
    if (depth <= 2) copy(freshFieldInvs = freshFieldInvs + inv)
    else this

  def recordConstrainedVar(arp: Var, constraint: Term): ActualFunctionRecorder =
    if (depth <= 2) copy(freshConstrainedVars = freshConstrainedVars + ((arp, constraint)))
    else this

  def recordConstraint(constraint: Term): ActualFunctionRecorder =
    if (depth <= 2) copy(freshConstraints = freshConstraints + constraint)
    else this

  def recordFreshSnapshot(snap: Function): ActualFunctionRecorder =
    if (depth <= 1) copy(freshSnapshots = freshSnapshots + snap)
    else this

  def recordPathSymbol(symbol: Function): ActualFunctionRecorder =
    if (depth <= 2) copy(freshPathSymbols = freshPathSymbols + symbol)
    else this

  def recordFreshMacro(decl: MacroDecl): FunctionRecorder =
    if (depth <= 1) copy(freshMacros = freshMacros + decl)
    else this

  def changeDepthBy(delta: Int): ActualFunctionRecorder =
    copy(depth = depth + delta)

  def merge(other: FunctionRecorder): ActualFunctionRecorder = {
    if (depth > 1) return this

    assert(other.getClass == this.getClass)
    assert(other.asInstanceOf[ActualFunctionRecorder]._data eq this._data)

    var lts = locToSnaps
    var fts = fappToSnaps

    if (depth == 0) {
      lts =
        other.locToSnaps.foldLeft(locToSnaps){case (accLts, (loc, guardsToSnaps)) =>
          val guardsToSnaps1 = accLts.getOrElse(loc, InsertionOrderedSet()) ++ guardsToSnaps
          accLts + (loc -> guardsToSnaps1)
        }

      fts =
        other.fappToSnaps.foldLeft(fappToSnaps){case (accFts, (fapp, guardsToSnaps)) =>
          val guardsToSnaps1 = accFts.getOrElse(fapp, InsertionOrderedSet()) ++ guardsToSnaps
          accFts + (fapp -> guardsToSnaps1)
        }
    }

    val fvfs = freshFvfsAndDomains ++ other.freshFvfsAndDomains
    val fieldInvs = freshFieldInvs ++ other.freshFieldInvs
    val arps = freshConstrainedVars ++ other.freshConstrainedVars
    val constraints = freshConstraints ++ other.freshConstraints
    val snaps = freshSnapshots ++ other.freshSnapshots
    val symbols = freshPathSymbols ++ other.freshPathSymbols
    val macros = freshMacros ++ other.freshMacros

    copy(locToSnaps = lts,
         fappToSnaps = fts,
         freshFvfsAndDomains = fvfs,
         freshFieldInvs = fieldInvs,
         freshConstrainedVars = arps,
         freshConstraints = constraints,
         freshSnapshots = snaps,
         freshPathSymbols = symbols,
         freshMacros = macros)
  }

  override lazy val toString: String = {
    val ltsStrs = locToSnaps map {case (k, v) => s"$k  |==>  $v"}
    val ftsStrs = fappToSnap map {case (k, v) => s"$k  |==>  $v"}

    s"""SnapshotRecorder(
        |  locToSnaps:
        |    ${ltsStrs.mkString("\n    ")}
        |  fappToSnap:
        |    ${ftsStrs.mkString("\n    ")}
        |  ...
        |)
     """.stripMargin
  }
}

case object NoopFunctionRecorder extends FunctionRecorder {
  val data: Option[FunctionData] = None
  private[functions] val fappToSnaps: Map[ast.FuncApp, InsertionOrderedSet[(Stack[Term], Term)]] = Map.empty
  val fappToSnap: Map[ast.FuncApp, Term] = Map.empty
  private[functions] val locToSnaps: Map[ast.LocationAccess, InsertionOrderedSet[(Stack[Term], Term)]] = Map.empty
  val locToSnap: Map[ast.LocationAccess, Term] = Map.empty
  val freshFvfsAndDomains: InsertionOrderedSet[SnapshotMapDefinition] = InsertionOrderedSet.empty
  val freshFieldInvs: InsertionOrderedSet[InverseFunctions] = InsertionOrderedSet.empty
  val freshConstrainedVars: InsertionOrderedSet[(Var, Term)] = InsertionOrderedSet.empty
  val freshConstraints: InsertionOrderedSet[Term] = InsertionOrderedSet.empty
  val freshSnapshots: InsertionOrderedSet[Function] = InsertionOrderedSet.empty
  val freshPathSymbols: InsertionOrderedSet[Function] = InsertionOrderedSet.empty
  val freshMacros: InsertionOrderedSet[MacroDecl] = InsertionOrderedSet.empty
  val depth = 0

  def merge(other: FunctionRecorder): NoopFunctionRecorder.type = {
    assert(other == this)

    this
  }

  def recordSnapshot(loc: ast.LocationAccess, guards: Stack[Term], snap: Term): NoopFunctionRecorder.type = this
  def recordFvfAndDomain(fvfDef: SnapshotMapDefinition): NoopFunctionRecorder.type = this
  def recordFieldInv(inv: InverseFunctions): NoopFunctionRecorder.type = this
  def recordSnapshot(fapp: ast.FuncApp, guards: Stack[Term], snap: Term): NoopFunctionRecorder.type = this
  def recordConstrainedVar(arp: Var, constraint: Term): NoopFunctionRecorder.type = this
  def recordConstraint(constraint: Term): NoopFunctionRecorder.type = this
  def recordFreshSnapshot(snap: Function): NoopFunctionRecorder.type = this
  def recordPathSymbol(symbol: Function): NoopFunctionRecorder.type = this
  def recordFreshMacro(decl: MacroDecl): NoopFunctionRecorder.type = this
  def changeDepthBy(delta: Int): NoopFunctionRecorder.type = this
}
