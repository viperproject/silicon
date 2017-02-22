/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package  viper.silicon.supporters.qps

import viper.silver.ast
import viper.silver.ast.{Predicate, Program}
import viper.silicon.Map
import viper.silicon.state.terms.{Sort, Var, sorts}
import viper.silicon.state.{Identifier, SymbolConverter, terms}
import viper.silver.components.StatefulComponent

class PredicateSnapGenerator(symbolConverter: SymbolConverter) extends StatefulComponent {
  var snapMap: Map[Predicate, terms.Sort] = Map()
  var formalVarMap: Map[Predicate, Seq[terms.Var]] = Map()

  def setup(program:Program): Unit =
    program visit {
      case ast.PredicateAccess(args, predname) =>
        val predicate = program.findPredicate(predname)
        val sort = predicate -> predicate.body.map(getOptimalSnapshotSort(_, program)._1).getOrElse(terms.sorts.Snap)
        val formalArgs:Seq[Var] = predicate.formalArgs.map(formalArg => Var(Identifier(formalArg.name), symbolConverter.toSort(formalArg.typ)))
        formalVarMap += predicate -> formalArgs
        snapMap += sort
    }

  def getSnap(predicate:Predicate): (terms.Sort, Boolean) =
    if (snapMap.contains(predicate)) {
      (snapMap(predicate), true)
    } else {
      (sorts.Snap, false)
    }

  def getArgs(predicate:Predicate): (Seq[terms.Var], Boolean) =
    if (formalVarMap.contains(predicate)) {
      (formalVarMap(predicate), true)
    } else {
      (Seq(), false)
    }

  /* TODO: The remainder of the file is an *identical* copy of code from the producer - merge it. */

  private def getOptimalSnapshotSort(a: ast.Exp, program: ast.Program, visited: scala.Seq[String] = Nil)
                                    : (Sort, Boolean) =

    a match {
      case _ if a.isPure =>
        (terms.sorts.Snap, true)

      case ast.AccessPredicate(locacc, _) => locacc match {
        case fa: ast.FieldAccess =>
          (symbolConverter.toSort(fa.field.typ), false)

        case pa: ast.PredicateAccess =>
          if (!visited.contains(pa.predicateName)) {
            program.findPredicate(pa.predicateName).body match {
              case None => (terms.sorts.Snap, false)
              case Some(body) => getOptimalSnapshotSort(body, program, pa.predicateName +: visited)
            }
          } else
          /* We detected a cycle in the predicate definition and thus stop
           * inspecting the predicate bodies.
           */
            (terms.sorts.Snap, false)
      }

      case ast.Implies(e0, a1) =>
        /* a1 must be impure, otherwise the first case would have applied. */
        getOptimalSnapshotSort(a1, program, visited)

      case ast.And(a1, a2) =>
        /* At least one of a1, a2 must be impure, otherwise ... */
        getOptimalSnapshotSortFromPair(a1, a2, () => (terms.sorts.Snap, false), program, visited)

      case ast.CondExp(_, a1, a2) =>
        /* At least one of a1, a2 must be impure, otherwise ... */

        def findCommonSort() = {
          val (s1, isPure1) = getOptimalSnapshotSort(a1, program, visited)
          val (s2, isPure2) = getOptimalSnapshotSort(a2, program, visited)
          val s = if (s1 == s2) s1 else terms.sorts.Snap
          val isPure = isPure1 && isPure2
          assert(!isPure)
          (s, isPure)
        }

        getOptimalSnapshotSortFromPair(a1, a2, findCommonSort, program, visited)

      case ast.utility.QuantifiedPermissions.QPForall(_, _, _, field, _, _, _) =>
        (terms.sorts.FieldValueFunction(symbolConverter.toSort(field.typ)), false)

      case _ =>
        (terms.sorts.Snap, false)
    }

  private def getOptimalSnapshotSortFromPair(a1: ast.Exp,
                                             a2: ast.Exp,
                                             fIfBothPure: () => (Sort, Boolean),
                                             program: ast.Program,
                                             visited: scala.Seq[String])
                                            : (Sort, Boolean) = {

    if (a1.isPure && a2.isPure) fIfBothPure()
    else (terms.sorts.Snap, false)
  }

  /* Lifecycle */

  def start(): Unit = {}

  def reset(): Unit = {
    snapMap = Map.empty
    formalVarMap = Map.empty
  }

  def stop(): Unit = {}
}
