// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.supporters

import java.io.File
import java.net.URL
import scala.annotation.unused
import scala.reflect.ClassTag
import viper.silver.ast
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.interfaces.PreambleContributor
import viper.silicon.interfaces.decider.ProverLike
import viper.silicon.state.DefaultSymbolConverter
import viper.silicon.state.terms._

abstract class BuiltinDomainsContributor extends PreambleContributor[Sort, DomainFun, Term] {
  type BuiltinDomainType <: ast.GenericType
  val builtinDomainTypeTag: ClassTag[BuiltinDomainType]

  def defaultSourceResource: String
  def userProvidedSourceFilepath: Option[String]

  lazy val sourceUrl: URL = {
    userProvidedSourceFilepath
      .map(filepath => new File(filepath).toURI.toURL)
      .getOrElse(getClass.getResource(defaultSourceResource))
  }

  def sourceDomainName: String
  def domainTranslator: DomainsTranslator[Term]
  def targetSortFactory(argumentSorts: Iterable[Sort]): Sort

  protected lazy val symbolConverter: BuiltinDomainAwareSymbolConverter =
    new BuiltinDomainAwareSymbolConverter(sourceDomainName, targetSortFactory)

  private var collectedSorts: InsertionOrderedSet[Sort] = InsertionOrderedSet.empty
  private var collectedFunctions = InsertionOrderedSet[DomainFun]()
  private var collectedAxioms = InsertionOrderedSet[Term]()

  /* Lifetime */

  def reset(): Unit = {
    collectedSorts = InsertionOrderedSet.empty
    collectedFunctions = InsertionOrderedSet.empty
    collectedAxioms = InsertionOrderedSet.empty
  }

  def start(): Unit = {}
  def stop(): Unit = {}

  /* Functionality */

  def analyze(program: ast.Program): Unit = {
    val builtinDomainTypeInstances = computeGroundTypeInstances(program)
    val sourceProgram = loadProgramFromUrl(sourceUrl)
    val sourceDomain = transformSourceDomain(sourceProgram.findDomain(sourceDomainName))

    // List of all domains found in the program with their instantiations, i.e. the types they are used with
    val sourceDomainTypeInstances =
      builtinDomainTypeInstances map (builtinTypeInstance => {
        val instantiation: Map[viper.silver.ast.TypeVar, viper.silver.ast.Type] = sourceDomain.typVars.zip(builtinTypeInstance.typeArguments).toMap
        ast.DomainType(sourceDomain, instantiation)
      })

    val sourceDomainInstantiationsWithType = instantiateWithDomain(sourceProgram, sourceDomain, sourceDomainTypeInstances)

    collectSorts(sourceDomainTypeInstances)
    collectFunctions(sourceDomainInstantiationsWithType, program)
    collectAxioms(sourceDomainInstantiationsWithType)
  }

  protected def computeGroundTypeInstances(program: ast.Program): InsertionOrderedSet[BuiltinDomainType] =
    InsertionOrderedSet(program.groundTypeInstances.collect {
      case builtinDomainTypeTag(s) => s
    })

  /**
   * For each necessary domain type, instantiate the corresponding domain
   */
  private def instantiateWithDomain(sourceProgram: ast.Program, sourceDomain: ast.Domain, sourceDomainTypeInstances: InsertionOrderedSet[ast.DomainType]): Set[(ast.DomainType, ast.Domain)] = {
    sourceDomainTypeInstances map (domainType => {
      /* TODO: Copied from DomainInstances.getInstanceMembers.
       *       Cannot directly use that because it filters according to which domain instances
       *       are used in the program from which the source domain was loaded, whereas the
       *       instances should be filtered according to which are used in the program under
       *       verification.
       */
      val functions = sourceDomain.functions.map(ast.utility.DomainInstances.substitute(_, domainType.typVarsMap, sourceProgram)).distinct
      val axioms = sourceDomain.axioms.map(ast.utility.DomainInstances.substitute(_, domainType.typVarsMap, sourceProgram)).distinct

      val instance = sourceDomain.copy(functions = functions, axioms = axioms)(sourceDomain.pos, sourceDomain.info, sourceDomain.errT)

      (domainType, transformSourceDomainInstance(instance, domainType))
    })
  }

  protected def transformSourceDomain(sourceDomain: ast.Domain): ast.Domain = sourceDomain

  protected def transformSourceDomainInstance(sourceDomain: ast.Domain, @unused typ: ast.DomainType): ast.Domain = sourceDomain

  protected def collectSorts(domainTypes: Iterable[ast.DomainType]): Unit = {
    assert(domainTypes forall (_.isConcrete), "Expected only concrete domain types")

    domainTypes.foreach(domainType => {
      val domainSort = symbolConverter.toSort(domainType)
      collectedSorts += domainSort
    })
  }

  protected def collectFunctions(domains: Set[(ast.DomainType, ast.Domain)], program: ast.Program): Unit = {
    domains foreach (d =>
      d._2.functions foreach (df =>
        if (df.interpretation.isEmpty)
          collectedFunctions += symbolConverter.toFunction(df, program).asInstanceOf[DomainFun]))
  }

  protected def collectAxioms(domains: Set[(ast.DomainType, ast.Domain)]): Unit = {
    domains foreach (d =>
      d._2.axioms foreach (ax =>
        collectedAxioms += translateAxiom(ax, d._1)))
  }

  protected def translateAxiom(ax: ast.DomainAxiom, d: ast.DomainType): Term = {
    /* Use builtin equality instead of the type-specific one.
     * Uses of custom equality functions, i.e. applications of the uninterpreted equality function,
     * are preserved.
     */
    val domainName = f"${d.domainName}[${d.typVarsMap.values.map(t => symbolConverter.toSort(t)).mkString(",")}]"
    domainTranslator.translateAxiom(ax, symbolConverter.toSort, builtin = true).transform {
      case q@Quantification(_,_,_,_,name,_,_) if name != "" =>
        q.copy(name = f"${domainName}_${name}")
      case Equals(t1, t2) => BuiltinEquals(t1, t2)
    }(recursive = _ => true)
  }

  def sortsAfterAnalysis: InsertionOrderedSet[Sort/*sorts.Multiset*/] = collectedSorts

  def declareSortsAfterAnalysis(sink: ProverLike): Unit = {
    sortsAfterAnalysis foreach (s => sink.declare(SortDecl(s)))
  }

  def symbolsAfterAnalysis: InsertionOrderedSet[DomainFun] =
    collectedFunctions

  def declareSymbolsAfterAnalysis(sink: ProverLike): Unit = {
    symbolsAfterAnalysis foreach (f => sink.declare(FunctionDecl(f)))
  }

  def axiomsAfterAnalysis: Iterable[Term] = collectedAxioms

  def emitAxiomsAfterAnalysis(sink: ProverLike): Unit = {
    sink.assumeAxioms(collectedAxioms, "Axioms from builtin domains contributor")
  }

  /* Utility */

  // TODO: Check that Silver's parser doesn't already provide suitable functionality.
  private def loadProgramFromUrl(url: URL): ast.Program = {
    assert(url != null, s"Unexpectedly found sourceUrl == null")

    val fromPath = viper.silver.utility.Paths.pathFromResource(url)
    val source = scala.io.Source.fromURL(url)

    val content =
      try {
        source.mkString
      } catch {
        case e@(_: RuntimeException | _: java.io.IOException) =>
          sys.error(s"Could not read from $url. Exception: $e")
      } finally {
        source.close()
      }

    val fp = new viper.silver.parser.FastParser()
    val parsedProgram = fp.parse(content, fromPath)
    assert(parsedProgram.errors.isEmpty, s"Unexpected parsing errors: ${parsedProgram.errors}")

    val resolver = viper.silver.parser.Resolver(parsedProgram)
    val resolved = resolver.run(false).get
    val translator = viper.silver.parser.Translator(resolved)
    val program = translator.translate.get

    program
  }
}

class BuiltinDomainAwareSymbolConverter(sourceDomainName: String,
                                        targetSortFactory: Iterable[Sort] => Sort)
    extends DefaultSymbolConverter {

  override def toSort(typ: ast.Type): Sort = typ match {
    case dt: ast.DomainType if dt.domainName == sourceDomainName =>
      targetSortFactory(dt.typVarsMap.values map toSort)
    case other =>
      super.toSort(other)
  }
}
