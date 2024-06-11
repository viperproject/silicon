// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

/* TODO: Large parts of this code are identical or at least very similar to the code that
 *       implements the support for quantified permissions to fields - merge it
 */

package  viper.silicon.supporters.qps

import viper.silver.ast
import viper.silver.ast.utility.QuantifiedPermissions.QuantifiedPermissionAssertion
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.{Config, Map}
import viper.silicon.interfaces.{PreambleContributor, PreambleReader}
import viper.silicon.interfaces.decider.{ProverLike, TermConverter}
import viper.silicon.state.MagicWandIdentifier
import viper.silicon.state.terms.{Sort, SortDecl, sorts}
import viper.silver.ast.PredicateAccess

trait PredicateSnapFunctionsContributor[SO, SY, AX] extends PreambleContributor[SO, SY, AX]

/** Creates background definitions for n-tuples of predicate and wand arguments. Currently,
  * snapshot trees are used to built n-tuples.
  *
  * TODO: Using snapshot trees to encode n-tuples of statically known size feels like a dirty
  *       hack. Consider predeclaring and using SMT datatypes instead.
  * TODO: It would be cleaner to have different tuple, trigger etc. classes for predicates and
  *       wands, including: this class, PredicateSnapFunction, PredicateTrigger, and others.
  * TODO: Previously, the functionality of this class was implemented via two classes,
  *       DefaultPredicateSnapFunctionsContributor and DefaultMagicWandSnapFunctionsContributor.
  *       Both needed to declare the same sort ($PSF<Snap>), but Silicon's architecture currently
  *       doesn't directly support filtering out such duplicates.
  *       This should be supported, however.
  *
  * @param preambleReader Used to read parametric preamble files with necessary background definitions.
  * @param termConverter Convert Silicon AST to prover's language, to contribute to its preamble.
  * @param predicateSnapGenerator Determines snapshot sort for predicate. TODO: Get rid of.
  * @param config Config to use.
  */
class DefaultPredicateAndWandSnapFunctionsContributor(preambleReader: PreambleReader[String, String],
                                                      termConverter: TermConverter[String, String, String],
                                                      predicateSnapGenerator: PredicateSnapGenerator,
                                                      config: Config)
    extends PredicateSnapFunctionsContributor[Sort, String, String] {

  /* PreambleBlock = Comment x Lines */
  private type PreambleBlock = (String, Iterable[String])

  private var collectedPredicates: InsertionOrderedSet[ast.Predicate] = InsertionOrderedSet.empty
  private var collectedWandIdentifiers: Set[MagicWandIdentifier] = InsertionOrderedSet.empty
  private var collectedSorts: InsertionOrderedSet[Sort] = InsertionOrderedSet.empty // TODO: Make Set[sorts.PredicateSnapFunction]
  private var collectedFunctionDecls: Iterable[PreambleBlock] = Seq.empty
  private var collectedAxioms: Iterable[PreambleBlock] = Seq.empty

  /* Lifetime */

  def reset(): Unit = {
    collectedPredicates = InsertionOrderedSet.empty
    collectedWandIdentifiers = InsertionOrderedSet.empty
    collectedSorts = InsertionOrderedSet.empty
    collectedFunctionDecls = Seq.empty
    collectedAxioms = Seq.empty
  }

  def stop(): Unit = {}

  def start(): Unit = {}

  /* Functionality */

  def analyze(program: ast.Program): Unit = {
    // TODO: Use next snippet instead?
    //   collectedPredicates =
    //     ast.utility.QuantifiedPermissions.quantifiedPredicates(program, program).toSet
    program visit {
      case QuantifiedPermissionAssertion(_, _, acc: ast.PredicateAccessPredicate) =>
        val predicate = program.findPredicate(acc.loc.predicateName)
        collectedPredicates += predicate
      case ast.Forall(_, triggers, _) =>
        val trigExps = triggers flatMap (_.exps)
        val predicateAccesses = trigExps flatMap (e => e.deepCollect {case pa: PredicateAccess => pa})
        collectedPredicates ++= (predicateAccesses map (_.loc(program)))
      case ast.Exists(_, triggers, _) =>
        val trigExps = triggers flatMap (_.exps)
        val predicateAccesses = trigExps flatMap (e => e.deepCollect { case pa: PredicateAccess => pa })
        collectedPredicates ++= (predicateAccesses map (_.loc(program)))
    }

    collectedWandIdentifiers =
      ast.utility.QuantifiedPermissions.quantifiedMagicWands(program, program)
        .map(MagicWandIdentifier(_, program))
        .toSet

    // WARNING: DefaultSetsContributor contributes a sort that is due to QPs over predicates and wands

    collectedSorts = collectedPredicates.map(predicate =>
        sorts.PredicateSnapFunction(predicateSnapGenerator.getSnap(predicate)._1, predicate.name)) ++ collectedWandIdentifiers.map(identifier => sorts.PredicateSnapFunction(sorts.Snap, identifier.toString))
    

    collectedFunctionDecls = generateFunctionDecls
    collectedAxioms = generateAxioms
  }

  private def extractPreambleLines(from: Iterable[PreambleBlock]*): Iterable[String] =
    from.flatten.flatMap(_._2)

  private def emitPreambleLines(sink: ProverLike, from: Iterable[PreambleBlock]*): Unit = {
    from.flatten foreach { case (comment, declarations) =>
      sink.comment(comment)
      sink.emit(declarations)
    }
  }

  def generateFunctionDecls: Iterable[PreambleBlock] = {
    val snapsTemplateFile = "/predicate_snap_functions_declarations.smt2"

    val predicatesPreamble =
      collectedPredicates map (p => {
        val snapSort = predicateSnapGenerator.getSnap(p)._1
        val id = p.name
        val substitutions = Map("$PRD$" -> id, "$S$" -> termConverter.convert(snapSort))
        val declarations = preambleReader.readParametricPreamble(snapsTemplateFile, substitutions)

        (s"$snapsTemplateFile [$id: $snapSort]", declarations)
      })

    val wandsPreamble =
      collectedWandIdentifiers map (wandIdentifier => {
        val snapSort = sorts.Snap
        val id = wandIdentifier.toString
        val substitutions = Map("$PRD$" -> id, "$S$" -> termConverter.convert(snapSort))
        val declarations = preambleReader.readParametricPreamble(snapsTemplateFile, substitutions)

        (s"$snapsTemplateFile [${wandIdentifier.ghostFreeWand}: $snapSort]", declarations)
      })

    predicatesPreamble ++ wandsPreamble
  }

  def generateAxioms: Iterable[PreambleBlock] = {
    val templateFile =
      if (config.disableISCTriggers()) "/predicate_snap_functions_axioms_no_triggers.smt2"
      else "/predicate_snap_functions_axioms.smt2"

    val predicatesPreamble =
      collectedPredicates map (p => {
        val sort = predicateSnapGenerator.getSnap(p)._1
        val id = p.name
        val substitutions = Map("$PRD$" -> id, "$S$" -> termConverter.convert(sort))
        val declarations = preambleReader.readParametricPreamble(templateFile, substitutions)

        (s"$templateFile [$id: $sort]", declarations)
      })

    val wandsPreamble =
      collectedWandIdentifiers map (wandIdentifier => {
        val sort = sorts.Snap // predicateSnapGenerator.getSnap(wandIdentifier)._1
        val id = wandIdentifier.toString
        val substitutions = Map("$PRD$" -> id, "$S$" -> termConverter.convert(sort))
        val declarations = preambleReader.readParametricPreamble(templateFile, substitutions)

        (s"$templateFile [$id: $sort]", declarations)
      })

    predicatesPreamble ++ wandsPreamble
  }

  def sortsAfterAnalysis: InsertionOrderedSet[Sort] = collectedSorts

  def declareSortsAfterAnalysis(sink: ProverLike): Unit = {
    sortsAfterAnalysis foreach (s => sink.declare(SortDecl(s)))
  }

  val symbolsAfterAnalysis: Iterable[String] =
    extractPreambleLines(collectedFunctionDecls)

  def declareSymbolsAfterAnalysis(sink: ProverLike): Unit =
    emitPreambleLines(sink, collectedFunctionDecls)

  val axiomsAfterAnalysis: Iterable[String] =
    extractPreambleLines(collectedAxioms)

  def emitAxiomsAfterAnalysis(sink: ProverLike): Unit =
    emitPreambleLines(sink, collectedAxioms)

  def updateGlobalStateAfterAnalysis(): Unit = { /* Nothing to contribute*/ }
}
