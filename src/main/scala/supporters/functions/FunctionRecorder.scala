/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.supporters.functions

import viper.silver.ast
import viper.silver.ast.{FuncApp, LocationAccess}
import viper.silicon.common.Mergeable
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.rules.{InverseFunction, PredicateInverseFunction}
import viper.silicon.{Map, Stack}
import viper.silicon.state.terms._
import viper.silicon.supporters.qps.{FvfDefinition, PsfDefinition}

trait FunctionRecorder extends Mergeable[FunctionRecorder] {
  def data: Option[FunctionData]
  private[functions] def locToSnaps: Map[ast.LocationAccess, InsertionOrderedSet[(Stack[Term], Term)]]
  def locToSnap: Map[ast.LocationAccess, Term]
  private[functions] def fappToSnaps: Map[ast.FuncApp, InsertionOrderedSet[(Stack[Term], Term)]]
  def fappToSnap: Map[ast.FuncApp, Term]
  def freshFvfsAndDomains: InsertionOrderedSet[(FvfDefinition, Seq[Term], Stack[Var])]
  def freshPsfsAndDomains: InsertionOrderedSet[(PsfDefinition, Seq[Term], Stack[Var])]
  def freshFieldInvs: InsertionOrderedSet[InverseFunction]
  def freshPredInvs: InsertionOrderedSet[PredicateInverseFunction]
  def freshArps: InsertionOrderedSet[(Var, Term)]
  def recordSnapshot(loc: ast.LocationAccess, guards: Stack[Term], snap: Term): FunctionRecorder
  def recordSnapshot(fapp: ast.FuncApp, guards: Stack[Term], snap: Term): FunctionRecorder
  def recordFvfAndDomain(fvf: FvfDefinition, domainDefinition: Seq[Term], qvars: Stack[Var]): FunctionRecorder
  def recordPsfAndDomain(psf: PsfDefinition, domainDefinition: Seq[Term], qvars: Stack[Var]): FunctionRecorder
  def recordFieldInv(inv: InverseFunction): FunctionRecorder
  def recordPredInv(inv: PredicateInverseFunction): FunctionRecorder
  def recordArp(arp: Var, constraint: Term): FunctionRecorder
}

case class ActualFunctionRecorder(private val _data: FunctionData,
                                  private[functions] val locToSnaps: Map[ast.LocationAccess, InsertionOrderedSet[(Stack[Term], Term)]] = Map(),
                                  private[functions] val fappToSnaps: Map[ast.FuncApp, InsertionOrderedSet[(Stack[Term], Term)]] = Map(),
                                  freshFvfsAndDomains: InsertionOrderedSet[(FvfDefinition, Seq[Term], Stack[Var])] = InsertionOrderedSet(),
                                  freshPsfsAndDomains: InsertionOrderedSet[(PsfDefinition, Seq[Term], Stack[Var])] = InsertionOrderedSet(),
                                  freshFieldInvs: InsertionOrderedSet[InverseFunction] = InsertionOrderedSet(),
                                  freshPredInvs: InsertionOrderedSet[PredicateInverseFunction] = InsertionOrderedSet(),
                                  freshArps: InsertionOrderedSet[(Var, Term)] = InsertionOrderedSet())
    extends FunctionRecorder {

  val data = Some(_data)

  def locToSnap: Map[ast.LocationAccess, Term] = {
    locToSnaps.map { case (loc, guardsToSnap) =>
      /* We (arbitrarily) make the snap of the head pair (guards -> snap) of
       * guardsToSnap the inner-most else-clause, i.e., we drop the guards.
       */
      val conditionalSnap =
        guardsToSnap.tail.foldLeft(guardsToSnap.head._2) { case (tailSnap, (guards, snap)) =>
          Ite(And(guards.toSet), snap, tailSnap)
        }

      loc -> conditionalSnap
    }
  }

  def fappToSnap: Map[ast.FuncApp, Term] = {
    fappToSnaps.map { case (fapp, guardsToSnap) =>
      /* We (arbitrarily) make the snap of the head pair (guards -> snap) of
       * guardsToSnap the inner-most else-clause, i.e., we drop the guards.
       */
      val conditionalSnap =
        guardsToSnap.tail.foldLeft(guardsToSnap.head._2) { case (tailSnap, (guards, snap)) =>
          Ite(And(guards.toSet), snap, tailSnap)
        }

      fapp -> conditionalSnap
    }
  }

  def recordSnapshot(loc: ast.LocationAccess, guards: Stack[Term], snap: Term) = {
    val guardsToSnaps = locToSnaps.getOrElse(loc, InsertionOrderedSet()) + (guards -> snap)
    copy(locToSnaps = locToSnaps + (loc -> guardsToSnaps))
  }

  def recordSnapshot(fapp: ast.FuncApp, guards: Stack[Term], snap: Term) = {
    val guardsToSnaps = fappToSnaps.getOrElse(fapp, InsertionOrderedSet()) + (guards -> snap)
    copy(fappToSnaps = fappToSnaps + (fapp -> guardsToSnaps))
  }

  def recordFvfAndDomain(fvf: FvfDefinition, domainDefinition: Seq[Term], qvars: Stack[Var]): FunctionRecorder =
    copy(freshFvfsAndDomains = freshFvfsAndDomains + ((fvf, domainDefinition, qvars)))

  def recordPsfAndDomain(psf: PsfDefinition, domainDefinition: Seq[Term], qvars: Stack[Var]): FunctionRecorder =
    copy(freshPsfsAndDomains= freshPsfsAndDomains + ((psf, domainDefinition, qvars)))

  def recordFieldInv(inv: InverseFunction): FunctionRecorder =
    copy(freshFieldInvs = freshFieldInvs + inv)

  def recordPredInv(inv: PredicateInverseFunction): FunctionRecorder =
    copy(freshPredInvs = freshPredInvs + inv)

  def recordArp(arp: Var, constraint: Term) = copy(freshArps = freshArps + ((arp, constraint)))

  def merge(other: FunctionRecorder): FunctionRecorder = {
    assert(other.getClass == this.getClass)
    assert(other.asInstanceOf[ActualFunctionRecorder]._data eq this._data)

    val lts =
      other.locToSnaps.foldLeft(locToSnaps){case (accLts, (loc, guardsToSnaps)) =>
        val guardsToSnaps1 = accLts.getOrElse(loc, InsertionOrderedSet()) ++ guardsToSnaps
        accLts + (loc -> guardsToSnaps1)
      }

    val fts =
      other.fappToSnaps.foldLeft(fappToSnaps){case (accFts, (fapp, guardsToSnaps)) =>
        val guardsToSnaps1 = accFts.getOrElse(fapp, InsertionOrderedSet()) ++ guardsToSnaps
        accFts + (fapp -> guardsToSnaps1)
      }

    val fvfs = freshFvfsAndDomains ++ other.freshFvfsAndDomains
    val psfs = freshPsfsAndDomains ++ other.freshPsfsAndDomains
    val fieldInvs = freshFieldInvs ++ other.freshFieldInvs
    val predInvs = freshPredInvs ++ other.freshPredInvs

    copy(locToSnaps = lts,
         fappToSnaps = fts,
         freshFvfsAndDomains = fvfs,
         freshPsfsAndDomains = psfs,
         freshFieldInvs = fieldInvs,
         freshPredInvs = predInvs)
  }

  override lazy val toString = {
    val ltsStrs = locToSnaps map {case (k, v) => s"$k  |==>  $v"}
    val ftsStrs = fappToSnap map {case (k, v) => s"$k  |==>  $v"}

    s"""SnapshotRecorder(
        |  locToSnaps:
        |    ${ltsStrs.mkString("\n    ")}
        |  fappToSnap:
        |    ${ftsStrs.mkString("\n    ")}
        |)
     """.stripMargin
  }
}

case object NoopFunctionRecorder extends FunctionRecorder {
  val data = None
  private[functions] val fappToSnaps: Map[FuncApp, InsertionOrderedSet[(Stack[Term], Term)]] = Map.empty
  val fappToSnap: Map[ast.FuncApp, Term] = Map.empty
  private[functions] val locToSnaps: Map[LocationAccess, InsertionOrderedSet[(Stack[Term], Term)]] = Map.empty
  val locToSnap: Map[ast.LocationAccess, Term] = Map.empty
  val freshFvfsAndDomains: InsertionOrderedSet[(FvfDefinition, Seq[Term], Stack[Var])] = InsertionOrderedSet.empty
  val freshPsfsAndDomains: InsertionOrderedSet[(PsfDefinition, Seq[Term], Stack[Var])] = InsertionOrderedSet.empty
  val freshFieldInvs: InsertionOrderedSet[InverseFunction] = InsertionOrderedSet.empty
  val freshPredInvs: InsertionOrderedSet[PredicateInverseFunction] = InsertionOrderedSet.empty
  val freshArps: InsertionOrderedSet[(Var, Term)] = InsertionOrderedSet.empty

  def merge(other: FunctionRecorder): FunctionRecorder = {
    assert(other == this)

    this
  }

  def recordSnapshot(loc: LocationAccess, guards: Stack[Term], snap: Term): FunctionRecorder = this
  def recordFvfAndDomain(fvf: FvfDefinition, domainDefinition: Seq[Term], qvars: Stack[Var]): FunctionRecorder = this
  def recordPsfAndDomain(psf: PsfDefinition, domainDefinition: Seq[Term], qvars: Stack[Var]): FunctionRecorder = this
  def recordFieldInv(inv: InverseFunction): FunctionRecorder = this
  def recordPredInv(inv: PredicateInverseFunction): FunctionRecorder = this
  def recordSnapshot(fapp: FuncApp, guards: Stack[Term], snap: Term): FunctionRecorder = this
  def recordArp(arp: Var, constraint: Term): FunctionRecorder = this
}
