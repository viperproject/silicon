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
  def freshArps: InsertionOrderedSet[(Var, Term)]
  def freshSnapshots: InsertionOrderedSet[Function]
  def freshPathSymbols: InsertionOrderedSet[Function]
  def freshMacros: InsertionOrderedSet[MacroDecl]
  def recordSnapshot(loc: ast.LocationAccess, guards: Stack[Term], snap: Term): FunctionRecorder
  def recordSnapshot(fapp: ast.FuncApp, guards: Stack[Term], snap: Term): FunctionRecorder
  def recordFvfAndDomain(fvfDef: SnapshotMapDefinition): FunctionRecorder
  def recordFieldInv(inv: InverseFunctions): FunctionRecorder
  def recordArp(arp: Var, constraint: Term): FunctionRecorder
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
                                  freshArps: InsertionOrderedSet[(Var, Term)] = InsertionOrderedSet(),
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
      /* We (arbitrarily) make the snap of the head pair (guards -> snap) of
       * guardsToSnap the inner-most else-clause, i.e. we drop the guards.
       */
      val conditionalSnap =
        guardsToSnap.tail.foldLeft(guardsToSnap.head._2) { case (tailSnap, (guards, snap)) =>
          Ite(And(guards.toSet), snap, tailSnap)
        }

      expr -> conditionalSnap
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
    if (depth <= 1) copy(freshFvfsAndDomains = freshFvfsAndDomains + fvfDef)
    else this

  def recordFieldInv(inv: InverseFunctions): ActualFunctionRecorder =
    if (depth <= 1) copy(freshFieldInvs = freshFieldInvs + inv)
    else this

  def recordArp(arp: Var, constraint: Term): ActualFunctionRecorder =
    if (depth <= 1) copy(freshArps = freshArps + ((arp, constraint)))
    else this

  def recordFreshSnapshot(snap: Function): ActualFunctionRecorder =
    if (depth <= 1) copy(freshSnapshots = freshSnapshots + snap)
    else this

  def recordPathSymbol(symbol: Function): ActualFunctionRecorder =
    if (depth <= 1) copy(freshPathSymbols = freshPathSymbols + symbol)
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
    val arps = freshArps ++ other.freshArps
    val snaps = freshSnapshots ++ other.freshSnapshots
    val symbols = freshPathSymbols ++ other.freshPathSymbols
    val macros = freshMacros ++ other.freshMacros

    copy(locToSnaps = lts,
         fappToSnaps = fts,
         freshFvfsAndDomains = fvfs,
         freshFieldInvs = fieldInvs,
         freshArps = arps,
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
  val freshArps: InsertionOrderedSet[(Var, Term)] = InsertionOrderedSet.empty
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
  def recordArp(arp: Var, constraint: Term): NoopFunctionRecorder.type = this
  def recordFreshSnapshot(snap: Function): NoopFunctionRecorder.type = this
  def recordPathSymbol(symbol: Function): NoopFunctionRecorder.type = this
  def recordFreshMacro(decl: MacroDecl): NoopFunctionRecorder.type = this
  def changeDepthBy(delta: Int): NoopFunctionRecorder.type = this
}
