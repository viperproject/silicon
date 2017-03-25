/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.supporters

import scala.reflect.{ClassTag, classTag}
import viper.silver.ast
import viper.silver.ast.{Program, SetType}
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.state.terms.{Sort, Term, sorts}

class DefaultSetsContributor(val domainTranslator: DomainsTranslator[Term])
    extends BuiltinDomainsContributor {

  type BuiltinDomainType = ast.SetType
  val builtinDomainTypeTag: ClassTag[BuiltinDomainType] = classTag[ast.SetType]

  val sourceResource: String = "/dafny_axioms/sets.vpr"
  def sourceDomainName: String = "$Set"

  override def computeGroundTypeInstances(program: Program): InsertionOrderedSet[SetType] = {
    var setTypeInstances = super.computeGroundTypeInstances(program)

    /* Axioms generated for quantified permissions depend on sets.
     * Hence, we add the appropriate set types iff quantified permissions are used in the program.
     *
     * TODO: It shouldn't be the responsibility of the sets contributor to add set types
     *       required by QPs
     */
    if (program.existsDefined { case q: ast.QuantifiedExp if !q.isPure => }) {
      program.fields foreach {f => setTypeInstances += ast.SetType(f.typ)}

      setTypeInstances += ast.SetType(ast.Ref) /* $FVF.domain_f is ref-typed */
    }

    setTypeInstances
  }

  def targetSortFactory(argumentSorts: Iterable[Sort]): Sort = {
    assert(argumentSorts.size == 1)
    sorts.Set(argumentSorts.head)
  }
}

//trait SetsContributor[SO, SY, AX] extends PreambleContributor[SO, SY, AX]
//
///* TODO: Shares a lot of implementation with DefaultSequencesContributor and other
// *       implementations of PreambleContributor - try to refactor
// */
//
//class DefaultSetsContributor(preambleReader: PreambleReader[String, String],
//                             symbolConverter: SymbolConverter,
//                             termConverter: TermConverter[String, String, String])
//    extends SetsContributor[sorts.Set, String, String] {
//
//  /* PreambleBlock = Comment x Lines */
//  private type PreambleBlock = (String, Iterable[String])
//
//  private var collectedSorts: InsertionOrderedSet[sorts.Set] = InsertionOrderedSet.empty
//  private var collectedFunctionDecls: Iterable[PreambleBlock] = Seq.empty
//  private var collectedAxioms: Iterable[PreambleBlock] = Seq.empty
//
//  /* Lifetime */
//
//  def reset() {
//    collectedSorts = InsertionOrderedSet.empty
//    collectedFunctionDecls = Seq.empty
//    collectedAxioms = Seq.empty
//  }
//
//  def start() {}
//  def stop() {}
//
//  /* Functionality */
//
//  def analyze(program: ast.Program) {
//    var setTypes = program.groundTypeInstances.collect{case s: ast.SetType => s}.to[InsertionOrderedSet]
//
//    /* Axioms generated for quantified permissions depend on sets.
//     * Hence, we add the appropriate set types iff quantified permissions are used in the program.
//     */
//    if (program.existsDefined { case q: ast.QuantifiedExp if !q.isPure => }) {
//      program.fields foreach {f => setTypes += ast.SetType(f.typ)}
//      setTypes += ast.SetType(ast.Ref) /* $FVF.domain_f is ref-typed */
//    }
//
//    collectedSorts = setTypes map (st => symbolConverter.toSort(st).asInstanceOf[sorts.Set])
//    collectedFunctionDecls = generateFunctionDecls
//    collectedAxioms = generateAxioms
//  }
//
//  private def extractPreambleLines(from: Iterable[PreambleBlock]*): Iterable[String] =
//    from.flatten.flatMap(_._2)
//
//  private def emitPreambleLines(sink: ProverLike, from: Iterable[PreambleBlock]*): Unit = {
//    from.flatten foreach { case (comment, declarations) =>
//      sink.comment(comment)
//      sink.emit(declarations)
//    }
//  }
//
//  def generateFunctionDecls: Iterable[PreambleBlock] = {
//    val templateFile = "/dafny_axioms/sets_declarations_dafny.smt2"
//
//    collectedSorts map {s =>
//      val substitutions = Map("$S$" -> termConverter.convert(s.elementsSort))
//      val declarations = preambleReader.readParametricPreamble(templateFile, substitutions)
//
//      (s"$templateFile [${s.elementsSort}]", declarations)
//    }
//  }
//
//  def generateAxioms: Iterable[PreambleBlock] = {
//    val templateFile = "/dafny_axioms/sets_axioms_dafny.smt2"
//
//    collectedSorts map {s =>
//      val substitutions = Map("$S$" -> termConverter.convert(s.elementsSort))
//      val declarations = preambleReader.readParametricPreamble(templateFile, substitutions)
//
//      (s"$templateFile [${s.elementsSort}]", declarations)
//    }
//  }
//
//  def sortsAfterAnalysis: InsertionOrderedSet[sorts.Set] = collectedSorts
//
//  def declareSortsAfterAnalysis(sink: ProverLike): Unit = {
//    sortsAfterAnalysis foreach (s => sink.declare(SortDecl(s)))
//  }
//
//  def symbolsAfterAnalysis: Iterable[String] =
//    extractPreambleLines(collectedFunctionDecls)
//
//  def declareSymbolsAfterAnalysis(sink: ProverLike): Unit =
//    emitPreambleLines(sink, collectedFunctionDecls)
//
//  def axiomsAfterAnalysis: Iterable[String] =
//    extractPreambleLines(collectedAxioms)
//
//  def emitAxiomsAfterAnalysis(sink: ProverLike): Unit =
//    emitPreambleLines(sink, collectedAxioms)
//
//  def updateGlobalStateAfterAnalysis(): Unit = { /* Nothing to contribute*/ }
//}
