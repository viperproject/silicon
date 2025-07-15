// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.supporters

import viper.silicon.debugger.DebugExp
import viper.silicon.state.terms.{Combine, First, Second, Sort, Term, Unit, sorts}
import viper.silicon.state.{MagicWandIdentifier, State, SymbolConverter}
import viper.silicon.utils.toSf
import viper.silicon.verifier.Verifier
import viper.silver.ast
import viper.silver.ast.Resource
import viper.silver.ast.utility.QuantifiedPermissions.QuantifiedPermissionAssertion

import scala.annotation.unused

trait SnapshotSupporter {
  def optimalSnapshotSort(a: ast.Exp, program: ast.Program): (Sort, Boolean)

  def optimalSnapshotSort(r: ast.Resource, s: State, v: Verifier): Sort

  def createSnapshotPair(s: State,
                         sf: (Sort, Verifier) => Term,
                         a0: ast.Exp,
                         a1: ast.Exp,
                         v: Verifier)
                        : ((Sort, Verifier) => Term, (Sort, Verifier) => Term)
}

class DefaultSnapshotSupporter(symbolConverter: SymbolConverter) extends SnapshotSupporter {
  def optimalSnapshotSort(a: ast.Exp, program: ast.Program): (Sort, Boolean) =
    optimalSnapshotSort(a, program, Nil)

  def optimalSnapshotSort(r: Resource, s: State, v: Verifier): Sort = r match {
    case f: ast.Field => v.symbolConverter.toSort(f.typ)
    case p: ast.Predicate if s.predicateSnapMap.contains(p) => s.predicateSnapMap(p)
    case p: ast.Predicate =>
      p.body.map(v.snapshotSupporter.optimalSnapshotSort(_, s.program)._1)
        .getOrElse(sorts.Snap)
    case mw: ast.MagicWand if s.qpMagicWands.contains(MagicWandIdentifier(mw, s.program)) =>
      sorts.Snap
    case _: ast.MagicWand => sorts.MagicWandSnapFunction
  }

  private def optimalSnapshotSort(a: ast.Exp, program: ast.Program, visited: Seq[String])
                                 : (Sort, Boolean) =

    a match {
      case _: ast.And if a.isPure =>
        (sorts.Snap, false)

      case _ if a.isPure =>
        (sorts.Snap, true)

      case ast.AccessPredicate(resacc, _) => resacc match {
        case fa: ast.FieldAccess =>
          (symbolConverter.toSort(fa.field.typ), false)

        case pa: ast.PredicateAccess =>
          if (!visited.contains(pa.predicateName)) {
            program.findPredicate(pa.predicateName).body match {
              case None => (sorts.Snap, false)
              case Some(body) => optimalSnapshotSort(body, program, pa.predicateName +: visited)
            }
          } else
          /* We detected a cycle in the predicate definition and thus stop
           * inspecting the predicate bodies.
           */
            (sorts.Snap, false)

        case _: ast.MagicWand =>
          (sorts.Snap, false)
      }

      case ast.Implies(_, a1) =>
        /* a1 must be impure, otherwise the first case would have applied. */
        optimalSnapshotSort(a1, program, visited)

      case ast.And(a1, a2) =>
        /* At least one of a1, a2 must be impure, otherwise ... */
        getOptimalSnapshotSortFromPair(a1, a2, () => (sorts.Snap, false))

      case ast.CondExp(_, a1, a2) =>
        /* At least one of a1, a2 must be impure, otherwise ... */

        def findCommonSort() = {
          val (s1, isPure1) = optimalSnapshotSort(a1, program, visited)
          val (s2, isPure2) = optimalSnapshotSort(a2, program, visited)
          val s = if (s1 == s2) s1 else sorts.Snap
          val isPure = isPure1 && isPure2
          assert(!isPure)
          (s, isPure)
        }

        getOptimalSnapshotSortFromPair(a1, a2, () => findCommonSort())

      case QuantifiedPermissionAssertion(_, _, acc: ast.FieldAccessPredicate) =>
        (sorts.FieldValueFunction(symbolConverter.toSort(acc.loc.field.typ), acc.loc.field.name), false)

      case _ =>
        (sorts.Snap, false)
    }

  private def getOptimalSnapshotSortFromPair(a1: ast.Exp,
                                             a2: ast.Exp,
                                             fIfBothPure: () => (Sort, Boolean))
                                            : (Sort, Boolean) = {

    if (a1.isPure && a2.isPure) fIfBothPure()
    else (sorts.Snap, false)
  }

  def createSnapshotPair(s: State,
                         sf: (Sort, Verifier) => Term,
                         a0: ast.Exp,
                         a1: ast.Exp,
                         v: Verifier)
                        : ((Sort, Verifier) => Term, (Sort, Verifier) => Term) = {

    val (snap0, snap1) = createSnapshotPair(s, sf(sorts.Snap, v), a0, a1, v)

    val sf0 = toSf(snap0)
    val sf1 = toSf(snap1)

    (sf0, sf1)
  }

  private def createSnapshotPair(@unused s: State, snap: Term, @unused a0: ast.Exp, @unused a1: ast.Exp, v: Verifier): (Term, Term) = {
    /* [2015-11-17 Malte] If both fresh snapshot terms and first/second datatypes
     * are used, then the overall test suite verifies in 2min 10sec, whereas
     * it takes 2min 20sec when only first/second datatypes are used. Might be
     * worth re-benchmarking from time to time.
     *
     * [2017-06-30 Nils] The performance difference seems to be negligible.
     * Using only first/second datatypes causes all/issues/carbon/0122.sil to fail,
     * though. Silicon produces the same output as Carbon in that case.
     *
     * [2019-12-22 Malte] The larger and more complex Silicon's test suite gets, the less
     * significant the performance difference becomes. I've therefore changed to implementation
     * to use First(snap)/Second(snap) as the default.
     */

    if (snap == Unit) {
      throw new IllegalArgumentException("Unit snapshot cannot be decomposed")
    }

    val (snap0, snap1, snapshotEq) =
      /* // [2019-12-22 Malte] Old code kept for documentation purposes
      if (!s.conservingSnapshotGeneration) {
        val snap0 = mkSnap(a0, Verifier.program, v)
        val snap1 = mkSnap(a1, Verifier.program, v)

        (snap0, snap1, snap === Combine(snap0, snap1))
      } else*/ {
        val snap0 = First(snap)
        val snap1 = Second(snap)

        (snap0, snap1, snap === Combine(snap0, snap1))
      }
    v.decider.assume(snapshotEq, Option.when(Verifier.config.enableDebugging())(DebugExp.createInstance("Snapshot", true)))

    (snap0, snap1)
  }
}
