/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.supporters

import viper.silver.ast
import viper.silicon.Map
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.interfaces.PreambleContributor
import viper.silicon.interfaces.decider.ProverLike
import viper.silicon.state.DefaultSymbolConverter
import viper.silicon.state.terms._

trait MultisetsContributor[SO, SY, AX] extends PreambleContributor[SO, SY, AX]

/* TODO: Shares a lot of implementation with DefaultSequencesEmitter. Refactor! */

class DefaultMultisetsContributor(domainTranslator: DomainsTranslator[Term])
    extends MultisetsContributor[Sort, DomainFun, Term] {

  private val symbolConverter = new BuiltinDomainAwareSymbolConverter()

  private var collectedSorts: InsertionOrderedSet[Sort] = InsertionOrderedSet.empty
  private var collectedFunctions = InsertionOrderedSet[DomainFun]()
  private var collectedAxioms = InsertionOrderedSet[Term]()

  /* Lifetime */

  def reset() {
    collectedSorts = InsertionOrderedSet.empty
    collectedFunctions = InsertionOrderedSet.empty
    collectedAxioms = InsertionOrderedSet.empty
  }

  def start() {}
  def stop() {}

  /* Functionality */

  def analyze(program: ast.Program) {
    val multisetTypes =
      program.groundTypeInstances.collect{case s: ast.MultisetType => s}.to[InsertionOrderedSet]

    val multisetDomainProgram =
      DefaultMultisetsContributor.loadProgram("/dafny_axioms/multisets.vpr")

    val multisetDomain = multisetDomainProgram.findDomain("$Multiset")

    val multisetDomainTypes =
      multisetTypes map (mt =>
        ast.DomainType(multisetDomain, Map(multisetDomain.typVars.head -> mt.elementType)))

    /* For each necessary domain type, instantiate the corresponding domain */
    val domainInstantiations =
      multisetDomainTypes map (mdt => {
        /* TODO: Copied from DomainInstances.getInstanceMembers.
         *       Cannot directly use that because it filters according to which domain instances
         *       are used in the program from which the multiset domain was loaded, whereas the
         *       instances should be filtered according to which are used in the program under
         *       verification.
         */
        val functions = multisetDomain.functions.map(ast.utility.DomainInstances.substitute(_, mdt.typVarsMap, multisetDomainProgram)).distinct
        val axioms = multisetDomain.axioms.map(ast.utility.DomainInstances.substitute(_, mdt.typVarsMap, multisetDomainProgram)).distinct

        multisetDomain.copy(_functions = functions, _axioms = axioms)(multisetDomain.pos, multisetDomain.info)
      })

    collectMultisetSorts(multisetDomainTypes)
    collectDomainMembers(domainInstantiations)
  }

  private def collectMultisetSorts(domainTypes: Iterable[ast.DomainType]) {
    assert(domainTypes forall (_.isConcrete), "Expected only concrete domain types")

    domainTypes.foreach(domainType => {
      val domainSort = symbolConverter.toSort(domainType)
      collectedSorts += domainSort
    })
  }

  private def collectDomainMembers(instantiatedDomains: Set[ast.Domain]) {
    instantiatedDomains foreach (domain => {
      domain.functions foreach (function =>
        collectedFunctions += symbolConverter.toFunction(function))

      domain.axioms foreach (axiom =>
        collectedAxioms += translateAxiom(axiom))
    })
  }

  private def translateAxiom(ax: ast.DomainAxiom): Term = {
    /* Use builtin equality instead of the type-specific one.
     * Uses of custom equality functions, e.g. Multiset_equals, are preserved.
     */
    domainTranslator.translateAxiom(ax, symbolConverter.toSort).transform {
      case Equals(t1, t2) => BuiltinEquals(t1, t2)
    }()
  }

  def sortsAfterAnalysis: InsertionOrderedSet[Sort/*sorts.Multiset*/] = collectedSorts

  def declareSortsAfterAnalysis(sink: ProverLike): Unit = {
    sortsAfterAnalysis foreach (s => sink.declare(SortDecl(s)))
  }

  def symbolsAfterAnalysis: InsertionOrderedSet[DomainFun] =
    collectedFunctions

  def declareSymbolsAfterAnalysis(sink: ProverLike): Unit = {
    collectedFunctions foreach (f => sink.declare(FunctionDecl(f)))
  }

  def axiomsAfterAnalysis: Iterable[Term] = collectedAxioms

  def emitAxiomsAfterAnalysis(sink: ProverLike): Unit = {
    collectedAxioms foreach (ax => sink.assume(ax))
  }

  def updateGlobalStateAfterAnalysis(): Unit = { /* Nothing to contribute*/ }
}

class BuiltinDomainAwareSymbolConverter extends DefaultSymbolConverter {
  override def toSort(typ: ast.Type): Sort = typ match {
    case dt: ast.DomainType if dt.domainName == "$Multiset" =>
      sorts.Multiset(toSort(dt.typVarsMap.values.head))
    case other =>
      super.toSort(other)
  }
}

private object DefaultMultisetsContributor {
  def loadProgram(fromResource: String): ast.Program = {
    val from = getClass.getResourceAsStream(fromResource)
    assert(from != null, s"Cannot find $fromResource")

    val fromPath = java.nio.file.Paths.get(getClass.getResource(fromResource).toURI)

    val source = scala.io.Source.fromInputStream(from)

    val content =
      try {
        source.mkString
      } catch {
        case e@(_: RuntimeException | _: java.io.IOException) =>
          sys.error(s"Could not read from $from. Exception: $e")
      } finally {
        source.close()
      }

    viper.silver.parser.FastParser.parse(content, fromPath) match {
      case fastparse.core.Parsed.Success(parsedProgram: viper.silver.parser.PProgram, _) =>
        assert(parsedProgram.errors.isEmpty, s"Unexpected parsing errors: ${parsedProgram.errors}")

        val resolver = viper.silver.parser.Resolver(parsedProgram)
        val resolved = resolver.run.get
        val translator = viper.silver.parser.Translator(resolved)
        val program = translator.translate.get

        program

      case fastparse.core.Parsed.Failure(msg, _, extra) =>
        sys.error(s"Failure: $msg, at ${viper.silver.parser.FilePosition(fromPath, extra.line, extra.col)}")
    }
  }
}
