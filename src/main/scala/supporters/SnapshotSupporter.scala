/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.supporters

import viper.silver.ast
import viper.silver.ast.utility.QuantifiedPermissions.QuantifiedPermissionAssertion
import viper.silicon.state.{State, SymbolConverter}
import viper.silicon.state.terms.{Combine, First, Second, Sort, Term, True, Unit, sorts}
import viper.silicon.utils.toSf
import viper.silicon.verifier.Verifier

trait SnapshotSupporter {
  def optimalSnapshotSort(a: ast.Exp, program: ast.Program): (Sort, Boolean)

  def createSnapshotPair(s: State,
                         sf: (Sort, Verifier) => Term,
                         a0: ast.Exp,
                         a1: ast.Exp,
                         v: Verifier)
                        : ((Sort, Verifier) => Term, (Sort, Verifier) => Term)

  def createSnapshotPair(s: State, snap: Term, a0: ast.Exp, a1: ast.Exp, v: Verifier)
                        : (Term, Term)
}

class DefaultSnapshotSupporter(symbolConverter: SymbolConverter) extends SnapshotSupporter {
  def optimalSnapshotSort(a: ast.Exp, program: ast.Program): (Sort, Boolean) =
    optimalSnapshotSort(a, program, Nil)

  private def optimalSnapshotSort(a: ast.Exp, program: ast.Program, visited: Seq[String])
                                 : (Sort, Boolean) =

    a match {
      case _ if a.isPure =>
        (sorts.Snap, true)

      case ast.AccessPredicate(locacc, _) => locacc match {
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
      }

      case ast.Implies(_, a1) =>
        /* a1 must be impure, otherwise the first case would have applied. */
        optimalSnapshotSort(a1, program, visited)

      case ast.And(a1, a2) =>
        /* At least one of a1, a2 must be impure, otherwise ... */
        getOptimalSnapshotSortFromPair(a1, a2, () => (sorts.Snap, false), program, visited)

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

        getOptimalSnapshotSortFromPair(a1, a2, findCommonSort, program, visited)

      case QuantifiedPermissionAssertion(_, _, acc: ast.FieldAccessPredicate) =>
        (sorts.FieldValueFunction(symbolConverter.toSort(acc.loc.field.typ)), false)

      case _ =>
        (sorts.Snap, false)
    }

  private def getOptimalSnapshotSortFromPair(a1: ast.Exp,
                                             a2: ast.Exp,
                                             fIfBothPure: () => (Sort, Boolean),
                                             program: ast.Program,
                                             visited: Seq[String])
                                            : (Sort, Boolean) = {

    if (a1.isPure && a2.isPure) fIfBothPure()
    else (sorts.Snap, false)
  }

  private def mkSnap(a: ast.Exp, program: ast.Program, v: Verifier, visited: Seq[String] = Nil): Term =
    optimalSnapshotSort(a, program, visited) match {
      case (sorts.Snap, true) => Unit
      case (sort, _) => v.decider.fresh(sort)
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

  def createSnapshotPair(s: State, snap: Term, a0: ast.Exp, a1: ast.Exp, v: Verifier): (Term, Term) = {
    /* [2015-11-17 Malte] If both fresh snapshot terms and first/second datatypes
     * are used, then the overall test suite verifies in 2min 10sec, whereas
     * it takes 2min 20sec when only first/second datatypes are used. Might be
     * worth re-benchmarking from time to time.
     */
    /* [2017-06-30 Nils] The performance difference seems to be negligible.
     * Using only first/second datatypes causes all/issues/carbon/0122.sil to fail,
     * though. Silicon produces the same output as Carbon in that case.
     */

    if (!s.conservingSnapshotGeneration) {
      val snap0 = mkSnap(a0, Verifier.program, v)
      val snap1 = mkSnap(a1, Verifier.program, v)

      val snapshotEq = (snap, snap0, snap1) match {
        case (Unit, Unit, Unit) => True()
        case (Unit, _, _) => sys.error(s"Unexpected equality between $s and ($snap0, $snap1)")
        case _ => snap === Combine(snap0, snap1)
      }

      v.decider.assume(snapshotEq)

      (snap0, snap1)
    } else {
      val _snap0 = First(snap)
      val _snap1 = Second(snap)

      (_snap0, _snap1)
    }
  }
}