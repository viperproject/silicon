/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.supporters

import viper.silver.ast
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.common.collections.immutable.MultiMap._
import viper.silicon.toMap
import viper.silicon.interfaces.PreambleContributor
import viper.silicon.interfaces.decider.ProverLike
import viper.silicon.state.{SymbolConverter, terms}
import viper.silicon.state.terms.{Distinct, DomainFun, Sort, Symbol, Term}

trait DomainsContributor[SO, SY, AX, UA] extends PreambleContributor[SO, SY, AX] {
  def uniquenessAssumptionsAfterAnalysis: Iterable[UA]
  def emitUniquenessAssumptionsAfterAnalysis(sink: ProverLike): Unit
}

class DefaultDomainsContributor(symbolConverter: SymbolConverter,
                                domainTranslator: DomainsTranslator[Term])
    extends DomainsContributor[Sort, DomainFun, Term, Term] {

  private var collectedSorts = InsertionOrderedSet[Sort]()
  private var collectedFunctions = InsertionOrderedSet[terms.DomainFun]()
  private var collectedAxioms = InsertionOrderedSet[Term]()
  private var uniqueSymbols = MultiMap.empty[Sort, Symbol]

  /* Lifetime */

  def reset() {
    collectedSorts = collectedSorts.empty
    collectedFunctions = collectedFunctions.empty
    collectedAxioms = collectedAxioms.empty
    uniqueSymbols = MultiMap.empty
  }

  def start() {}
  def stop() {}

  /* Functionality */

  def analyze(program: ast.Program) {
    /* Compute necessary instances of all user-declared Viper domains */
    val necessaryDomainTypes = program.groundTypeInstances.collect{case d: ast.DomainType => d}

    /* A map from domain names to domain nodes */
    val domainNameMap = toMap(program.domains.map(d => d.name -> d))

    /* For each necessary domain type, instantiate the corresponding domain */
    val instantiatedDomains =
      necessaryDomainTypes map (cdt => domainNameMap(cdt.domainName).instantiate(cdt, program))

    collectDomainSorts(necessaryDomainTypes)
    collectDomainMembers(instantiatedDomains)
  }

  private def collectDomainSorts(domainTypes: Iterable[ast.DomainType]) {
    assert(domainTypes forall (_.isConcrete), "Expected only concrete domain types")

    domainTypes.foreach(domainType => {
      val domainSort = symbolConverter.toSort(domainType)
      collectedSorts += domainSort
    })
  }

  private def collectDomainMembers(instantiatedDomains: Set[ast.Domain]) {
    /* Since domain member instances come with Silver types, but the corresponding prover
     * declarations work with Silicon sorts, it can happen that two instances with different types
     * result in the same function declaration because the types are mapped to the same sort(s).
     *
     * Another source of potential declaration duplication is, that the set of domain member
     * instances can contain two function instances where the type variable mapping of one
     * instance is a subset of the mapping of the other. For example:
     *   function foo(a: A): Int    with (A -> Int)
     *   function foo(a: A): Int    with (A -> Int, B -> Ref)
     * This can happen if the declaring domain contains more type variables than are used by the
     * function.
     */

    instantiatedDomains foreach (domain => {
      domain.functions foreach (function => {
        val fct = symbolConverter.toFunction(function)

        collectedFunctions += fct

        if (function.unique) {
          assert(function.formalArgs.isEmpty,
            s"Expected unique domain functions to not take arguments, but found $function")

          uniqueSymbols = uniqueSymbols.addBinding(fct.resultSort, fct)
        }
      })

      domain.axioms foreach (axiom => {
        val tAx = domainTranslator.translateAxiom(axiom, symbolConverter.toSort)
        collectedAxioms += tAx
      })
    })
  }

  def sortsAfterAnalysis: Iterable[terms.Sort] = collectedSorts

  def declareSortsAfterAnalysis(sink: ProverLike): Unit = {
    collectedSorts foreach (s => sink.declare(terms.SortDecl(s)))
  }

  def symbolsAfterAnalysis: Iterable[terms.DomainFun] = collectedFunctions

  def declareSymbolsAfterAnalysis(sink: ProverLike): Unit = {
    collectedFunctions foreach (f => sink.declare(terms.FunctionDecl(f)))
  }

  def axiomsAfterAnalysis: Iterable[terms.Term] = collectedAxioms

  def emitAxiomsAfterAnalysis(sink: ProverLike): Unit = {
    collectedAxioms foreach (ax => sink.assume(ax))
  }

  def uniquenessAssumptionsAfterAnalysis: Iterable[Term] =
    uniqueSymbols.map.values map Distinct

  def emitUniquenessAssumptionsAfterAnalysis(sink: ProverLike): Unit = {
    uniquenessAssumptionsAfterAnalysis foreach (t => sink.assume(t))
  }

  def updateGlobalStateAfterAnalysis(): Unit = { /* Nothing to contribute*/ }
}

trait DomainsTranslator[R] {
  def translateAxiom(ax: ast.DomainAxiom, toSort: ast.Type => Sort): R
}

class DefaultDomainsTranslator()
    extends DomainsTranslator[Term]
       with ExpressionTranslator {

  def translateAxiom(ax: ast.DomainAxiom, toSort: ast.Type => Sort): Term = {
    translate(toSort)(ax.exp) match {
      case terms.Quantification(q, vars, body, triggers, "", _) =>
        terms.Quantification(q, vars, body, triggers, s"prog.${ax.name}")

      case other => other
    }
  }
}
