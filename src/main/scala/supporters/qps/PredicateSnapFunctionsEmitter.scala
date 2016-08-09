/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package supporters.qps

import viper.silver.ast
import viper.silicon.{Config, Map, toSet, Set}
import viper.silicon.decider.PreambleFileEmitter
import viper.silicon.interfaces.PreambleEmitter
import viper.silicon.interfaces.decider.Prover
import viper.silicon.state.terms.{SortDecl, Function, Sort}
import viper.silicon.state.{terms, SymbolConvert}

trait PredicateSnapFunctionsEmitter extends PreambleEmitter
/*
class DefaultFieldValueFunctionsEmitter(prover: => Prover,
                                        symbolConverter: SymbolConvert,
                                        preambleFileEmitter: PreambleFileEmitter[String, String],
                                        config: Config)
    extends PredicateSnapFunctionsEmitter {

  private var collectedPredicates = Set[ast.Predicate]()
  private var collectedSorts = Set[terms.sorts.PredicateSnapFunction]()

  def sorts: Set[Sort] = toSet(collectedSorts)
  /* Scala's immutable sets are invariant in their element type, hence
   * Set[FVF] is not a subtype of Set[Sort], although FVF is one of Sort.
   */

  def analyze(program: ast.Program) {
    program visit {
      case ast.utility.QuantifiedPermissions.QPPForall(_, _, _, _, _, _, predAccpred) =>
        collectedPredicates += program.findPredicate(predAccpred.loc.predicateName)
    }

    collectedSorts = (
        collectedPredicates.map(predicate => terms.sorts.PredicateSnapFunction(predicate.typ)
      )
  }

  def declareSorts() {
    collectedSorts foreach (s => prover.declare(SortDecl(s)))
  }

  def declareSymbols() {
    collectedPredicates foreach { predicate =>
      val sort = symbolConverter.toSort(predicate.typ)
      val id = predicate.name
      val substitutions = Map("$FLD$" -> id, "$S$" -> prover.termConverter.convert(sort))

      val fvfDeclarations = "/field_value_functions_declarations.smt2"
      prover.logComment(s"$fvfDeclarations [$id: $sort]")
      preambleFileEmitter.emitParametricAssertions(fvfDeclarations, substitutions)
    }
  }

  def emitAxioms() {
    /* Axioms that have to be emitted for each field that is dereferenced from
     * a quantified receiver
     */
    collectedPredicates foreach { predicate =>
      val sort = symbolConverter.toSort(predicate.typ)
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
*/