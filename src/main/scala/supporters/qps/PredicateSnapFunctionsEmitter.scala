/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package  viper.silicon.supporters.qps

import viper.silver.ast
import viper.silver.ast.{Predicate, Program, PredicateAccess}
import viper.silicon.{Config, Map, Set, toSet}
import viper.silicon.decider.PreambleFileEmitter
import viper.silicon.interfaces.PreambleEmitter
import viper.silicon.interfaces.decider.Prover
import viper.silicon.state.terms.{sorts, _}
import viper.silicon.state.terms.sorts._
import viper.silicon.state.{SymbolConvert, terms}
import viper.silicon.interfaces.{Consumer, Evaluator, Failure, Producer, VerificationResult}

trait PredicateSnapFunctionsEmitter extends PreambleEmitter

class DefaultPredicateSnapFunctionsEmitter(prover: => Prover,
                                        symbolConverter: SymbolConvert,
                                        preambleFileEmitter: PreambleFileEmitter[String, String],
                                        config: Config
                                          )
    extends PredicateSnapFunctionsEmitter {


  private var collectedPredicates = Set[Predicate]()
  private var collectedSorts = Set[terms.sorts.PredicateSnapFunction]()
  private var snapMap:Map[Predicate, terms.Sort] = Map()
  private var argTypeMap: Map[Predicate, terms.Sort] = Map()

  def sorts: Set[Sort] = toSet(collectedSorts)
  /* Scala's immutable sets are invariant in their element type, hence
   * Set[FVF] is not a subtype of Set[Sort], although FVF is one of Sort.
   */


  def analyze(program: ast.Program) {
    program visit {
      case ast.utility.QuantifiedPermissions.QPPForall(_, _, _, _, _, _, predAccpred) =>
        val predicate = program.findPredicate(predAccpred.loc.predicateName)
        val sort = (predicate -> predicate.body.map(getOptimalSnapshotSort(_, program)._1).getOrElse(terms.sorts.Snap))
        //val argSnap:Term = predAccpred.loc.args.reduce((arg1:Term, arg2:Term) => terms.Combine(arg1, arg2))
        collectedPredicates += predicate
        snapMap += sort
        //argTypeMap += (predicate -> argSnap.sort)
    }


      collectedSorts = (
        collectedPredicates.map(predicate => terms.sorts.PredicateSnapFunction((predicate.body.map(getOptimalSnapshotSort(_, program)._1).getOrElse(terms.sorts.Snap))))
          + terms.sorts.PredicateSnapFunction(terms.sorts.Snap)
      )


  }

  def declareSorts() {
    prover.declare(SortDecl(terms.sorts.Set(terms.sorts.Snap)))
    collectedSorts foreach (s => prover.declare(SortDecl(s)))
}

  def declareSymbols() {
    //declare Set properties
    val setDecl = "/dafny_axioms/sets_declarations_dafny.smt2"
    val setSort = terms.sorts.Snap
    val substitutions = Map("$S$" -> prover.termConverter.convert(setSort))
    prover.logComment(s"$setDecl [$setSort")
    preambleFileEmitter.emitParametricAssertions(setDecl, substitutions)


    collectedPredicates foreach { predicate =>
      val sort = snapMap(predicate)
      val sort2 = prover.termConverter.convert(terms.sorts.Snap)
      val id = predicate.name
      val substitutions = Map("$PRD$" -> id, "$S$" -> prover.termConverter.convert(sort))

      val psfDeclarations = "/predicate_snap_functions_declarations.smt2"
      prover.logComment(s"$psfDeclarations [$id: $sort: $sort2]")
      preambleFileEmitter.emitParametricAssertions(psfDeclarations, substitutions)
    }
  }

  def emitAxioms() {
    /* Axioms that have to be emitted for each field that is dereferenced from
     * a quantified receiver
     */


    collectedPredicates foreach { predicate =>
      val sort = snapMap(predicate)
      val id = predicate.name
      val psfSubstitutions = Map("$PRD$" -> id, "$S$" -> prover.termConverter.convert(sort))
      val psfAxioms = if (config.disableISCTriggers()) "/predicate_snap_functions_axioms_no_triggers.smt2" else "/predicate_snap_functions_axioms.smt2"

      prover.logComment(s"$psfAxioms [$id: $sort]")
      preambleFileEmitter.emitParametricAssertions(psfAxioms, psfSubstitutions)
    }
  }

  /* Lifetime */

  def reset() {
    collectedPredicates = collectedPredicates.empty
    snapMap = snapMap.empty
  }

  def stop() {}
  def start() {}


  private def getOptimalSnapshotSort(φ: ast.Exp, program: ast.Program, visited: scala.Seq[String] = Nil)
  : (Sort, Boolean) =

    φ match {
      case _ if φ.isPure =>
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

      case ast.Implies(e0, φ1) =>
        /* φ1 must be impure, otherwise the first case would have applied. */
        getOptimalSnapshotSort(φ1, program, visited)

      case ast.And(φ1, φ2) =>
        /* At least one of φ1, φ2 must be impure, otherwise ... */
        getOptimalSnapshotSortFromPair(φ1, φ2, () => (terms.sorts.Snap, false), program, visited)

      case ast.CondExp(_, φ1, φ2) =>
        /* At least one of φ1, φ2 must be impure, otherwise ... */

        def findCommonSort() = {
          val (s1, isPure1) = getOptimalSnapshotSort(φ1, program, visited)
          val (s2, isPure2) = getOptimalSnapshotSort(φ2, program, visited)
          val s = if (s1 == s2) s1 else terms.sorts.Snap
          val isPure = isPure1 && isPure2
          assert(!isPure)
          (s, isPure)
        }

        getOptimalSnapshotSortFromPair(φ1, φ2, findCommonSort, program, visited)

      case ast.utility.QuantifiedPermissions.QPForall(_, _, _, field, _, _, _) =>
        (terms.sorts.FieldValueFunction(symbolConverter.toSort(field.typ)), false)

      case _ =>
        (terms.sorts.Snap, false)
    }

  private def getOptimalSnapshotSortFromPair(φ1: ast.Exp,
                                             φ2: ast.Exp,
                                             fIfBothPure: () => (Sort, Boolean),
                                             program: ast.Program,
                                             visited: scala.Seq[String])
  : (Sort, Boolean) = {

    if (φ1.isPure && φ2.isPure) fIfBothPure()
    else (terms.sorts.Snap, false)
  }
}
