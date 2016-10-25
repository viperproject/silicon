/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

/* TODO: Large parts of this code are identical or at least very similar to the code that
 *       implements the support for quantified permissions to fields - merge it
 */

package  viper.silicon.supporters.qps

import viper.silver.ast
import viper.silver.ast.{Predicate}
import viper.silicon.{Config, Map, Set, toSet}
import viper.silicon.decider.PreambleFileEmitter
import viper.silicon.interfaces.PreambleEmitter
import viper.silicon.interfaces.decider.Prover
import viper.silicon.state.terms._
import viper.silicon.state.{SymbolConvert, terms}

trait PredicateSnapFunctionsEmitter extends PreambleEmitter

class DefaultPredicateSnapFunctionsEmitter(prover: => Prover,
                                        symbolConverter: SymbolConvert,
                                        predicateSnapGenerator: PredicateSnapGenerator,
                                        preambleFileEmitter: PreambleFileEmitter[String, String],
                                        config: Config
                                          )
    extends PredicateSnapFunctionsEmitter {


  private var collectedPredicates = Set[Predicate]()
  private var collectedSorts = Set[terms.sorts.PredicateSnapFunction]()

  def sorts: Set[Sort] = toSet(collectedSorts)
  /* Scala's immutable sets are invariant in their element type, hence
   * Set[PSF] is not a subtype of Set[Sort], although PSF is one of Sort.
   */


  def analyze(program: ast.Program) {
    program visit {
      case ast.utility.QuantifiedPermissions.QPPForall(_, _, _, _, _, _, predAccpred) =>
        val predicate = program.findPredicate(predAccpred.loc.predicateName)
        collectedPredicates += predicate
    }

      collectedSorts = (
        collectedPredicates.map(predicate => terms.sorts.PredicateSnapFunction(predicateSnapGenerator.getSnap(predicate)._1))
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
      val sort = predicateSnapGenerator.getSnap(predicate)._1
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
      val sort = predicateSnapGenerator.getSnap(predicate)._1
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
  }

  def stop() {}
  def start() {}
}
