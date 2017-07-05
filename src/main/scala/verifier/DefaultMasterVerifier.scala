/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.verifier

import java.text.SimpleDateFormat
import java.util.concurrent._

import viper.silver.ast
import viper.silver.components.StatefulComponent
import viper.silicon._
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.decider.SMTLib2PreambleReader
import viper.silicon.interfaces._
import viper.silicon.interfaces.decider.ProverLike
import viper.silicon.state._
import viper.silicon.state.terms.{Decl, Sort, Term, sorts}
import viper.silicon.supporters._
import viper.silicon.supporters.functions.DefaultFunctionVerificationUnitProvider
import viper.silicon.supporters.qps._
import viper.silicon.utils.Counter

/* TODO: Extract a suitable MasterVerifier interface, probably including
 *         - def verificationPoolManager: VerificationPoolManager)
 *         - def uniqueIdCounter: String)
 */

trait MasterVerifier extends Verifier {
  def nextUniqueVerifierId(): String
  def verificationPoolManager: VerificationPoolManager
}

class DefaultMasterVerifier(config: Config)
    extends BaseVerifier(config, "00")
       with MasterVerifier
       with DefaultFunctionVerificationUnitProvider
       with DefaultPredicateVerificationUnitProvider {

  Verifier.config = config

  private val uniqueIdCounter = new Counter(1)
  def nextUniqueVerifierId(): String = f"${uniqueIdCounter.next()}%02d"

  protected val preambleReader = new SMTLib2PreambleReader

  protected val sequencesContributor = new DefaultSequencesContributor(preambleReader, symbolConverter, termConverter)
  protected val setsContributor = new DefaultSetsContributor(domainTranslator)
  protected val multisetsContributor = new DefaultMultisetsContributor(domainTranslator)
  protected val domainsContributor = new DefaultDomainsContributor(symbolConverter, domainTranslator)
  protected val fieldValueFunctionsContributor = new DefaultFieldValueFunctionsContributor(preambleReader, symbolConverter, termConverter, config)
  protected val predSnapGenerator = new PredicateSnapGenerator(symbolConverter, snapshotSupporter)
  protected val predicateSnapFunctionsContributor = new DefaultPredicateSnapFunctionsContributor(preambleReader, symbolConverter, termConverter, predSnapGenerator, config)

  private val _verificationPoolManager: VerificationPoolManager = new VerificationPoolManager(this)
  def verificationPoolManager: VerificationPoolManager = _verificationPoolManager

  private val statefulSubcomponents = List[StatefulComponent](
    uniqueIdCounter,
    sequencesContributor, setsContributor, multisetsContributor, domainsContributor,
    fieldValueFunctionsContributor,
    predSnapGenerator, predicateSnapFunctionsContributor,
    functionsSupporter, predicateSupporter,
    _verificationPoolManager
  )

  /* Lifetime */

  override def start() {
    super.start()
    statefulSubcomponents foreach (_.start())
  }

  override def reset() {
    super.reset()
    statefulSubcomponents foreach (_.reset())
  }

  override def stop() {
    super.stop()
    statefulSubcomponents foreach (_.stop())
  }

  /* Verifier orchestration */

  private object allProvers extends ProverLike {
    def emit(content: String): Unit = {
      decider.prover.emit(content)
      _verificationPoolManager.pooledVerifiers.emit(content)
    }

    def assume(term: Term): Unit = {
      decider.prover.assume(term)
      _verificationPoolManager.pooledVerifiers.assume(term)
    }

    def declare(decl: Decl): Unit = {
      decider.prover.declare(decl)
      _verificationPoolManager.pooledVerifiers.declare(decl)
    }

    def comment(content: String): Unit = {
      decider.prover.comment(content)
      _verificationPoolManager.pooledVerifiers.comment(content)
    }
  }

  /* Program verification */

  def verify(_program: ast.Program): List[VerificationResult] = {
    /** Trigger computation is currently not thread-safe; hence, all triggers are computed
      * up-front, before the program is verified in parallel.
      * See also [[viper.silicon.utils.ast.autoTrigger]].
      */
    val program = _program.transform {
      case forall: ast.Forall if forall.isPure => viper.silicon.utils.ast.autoTrigger(forall)
    }

    if (config.printTranslatedProgram()) {
      println(program)
    }

    Verifier.program = program

    predSnapGenerator.setup(program) // TODO: Why did Nadja put this here?


    allProvers.comment("Started: " + new SimpleDateFormat("yyyy-MM-dd HH:mm:ss").format(System.currentTimeMillis()) /*bookkeeper.formattedStartTime*/)
    allProvers.comment("Silicon.buildVersion: " + Silicon.buildVersion)
    allProvers.comment(s"Input file: ${config.inputFile.getOrElse("<unknown>")}")
    allProvers.comment(s"Verifier id: $uniqueId")
    allProvers.comment("-" * 60)
    allProvers.comment("Begin preamble")

    allProvers.comment("/" * 10 + " Static preamble")
    emitStaticPreamble(allProvers)

    analyzeProgramAndEmitPreambleContributions(program, allProvers)

    allProvers.comment("End preamble")
    allProvers.comment("-" * 60)


    SymbExLogger.resetMemberList()
    SymbExLogger.setConfig(config)

    /* TODO: A workaround for Silver issue #94. toList must be before flatMap.
     *       Otherwise Set will be used internally and some error messages will be lost.
     */
    val functionVerificationResults = functionsSupporter.units.toList flatMap (function => {
      val res = functionsSupporter.verify(createInitialState(function, program), function)
//      bookkeeper.functionVerified(function.name)
      res
    })

    val predicateVerificationResults = predicateSupporter.units.toList flatMap (predicate =>{
      val res = predicateSupporter.verify(createInitialState(predicate, program), predicate)
//      bookkeeper.predicateVerified(predicate.name)
      res
    })

    decider.prover.stop()

    _verificationPoolManager.pooledVerifiers.comment("-" * 60)
    _verificationPoolManager.pooledVerifiers.comment("Begin function- and predicate-related preamble")
    predicateSupporter.declareSortsAfterVerification(_verificationPoolManager.pooledVerifiers)
    functionsSupporter.declareSortsAfterVerification(_verificationPoolManager.pooledVerifiers)
    predicateSupporter.declareSymbolsAfterVerification(_verificationPoolManager.pooledVerifiers)
    functionsSupporter.declareSymbolsAfterVerification(_verificationPoolManager.pooledVerifiers)
    predicateSupporter.emitAxiomsAfterVerification(_verificationPoolManager.pooledVerifiers)
    functionsSupporter.emitAxiomsAfterVerification(_verificationPoolManager.pooledVerifiers)
    _verificationPoolManager.pooledVerifiers.comment("End function- and predicate-related preamble")
    _verificationPoolManager.pooledVerifiers.comment("-" * 60)

    val verificationTaskFutures: Seq[Future[Seq[VerificationResult]]] =
      program.methods.filterNot(excludeMethod).map(method => {
        val s = createInitialState(method, program)/*.copy(parallelizeBranches = true)*/ /* [BRANCH-PARALLELISATION] */
        _verificationPoolManager.queueVerificationTask(v => v.methodSupporter.verify(s, method))
      })

    val methodVerificationResults = verificationTaskFutures.flatMap(_.get())

    /** Write JavaScript-Representation of the log if the SymbExLogger is enabled */
    SymbExLogger.writeJSFile()
    /** Write DOT-Representation of the log if the SymbExLogger is enabled */
    SymbExLogger.writeDotFile()

    (   functionVerificationResults
     ++ predicateVerificationResults
     ++ methodVerificationResults)
  }

  private def createInitialState(member: ast.Member, program: ast.Program): State = {
    val quantifiedFields = InsertionOrderedSet(ast.utility.QuantifiedPermissions.quantifiedFields(member, program))
    val quantifiedPredicates = InsertionOrderedSet(ast.utility.QuantifiedPermissions.quantifiedPredicates(member, program))
    val applyHeuristics = program.fields.exists(_.name.equalsIgnoreCase("__CONFIG_HEURISTICS"))

    State(qpFields = quantifiedFields,
          qpPredicates = quantifiedPredicates,
          applyHeuristics = applyHeuristics,
          predicateSnapMap = predSnapGenerator.snapMap,
          predicateFormalVarMap = predSnapGenerator.formalVarMap)
  }

  private def excludeMethod(method: ast.Method) = (
       !method.name.matches(config.includeMethods())
    || method.name.matches(config.excludeMethods()))

  /* Prover preamble: Static preamble */

  private def emitStaticPreamble(sink: ProverLike) {
    sink.comment("\n; /z3config.smt2")
    preambleReader.emitPreamble("/z3config.smt2", sink)

    val smt2ConfigOptions =
      config.z3ConfigArgs().map { case (k, v) => s"(set-option :$k $v)" }

    if (smt2ConfigOptions.nonEmpty) {
      logger.info(s"Additional Z3 configuration options are '${config.z3ConfigArgs()}'")
      preambleReader.emitPreamble(smt2ConfigOptions, sink)
    }

    sink.comment("\n; /preamble.smt2")
    preambleReader.emitPreamble("/preamble.smt2", sink)
  }

  /* Prover preamble: After program analysis */

  private val analysisOrder: Seq[PreambleContributor[_, _, _]] = Seq(
    sequencesContributor,
    setsContributor,
    multisetsContributor,
    domainsContributor,
    fieldValueFunctionsContributor,
    predicateSnapFunctionsContributor,
    functionsSupporter,
    predicateSupporter
  )

  private val sortDeclarationOrder: Seq[PreambleContributor[_, _, _]] = Seq(
    sequencesContributor,
    setsContributor,
    multisetsContributor,
    domainsContributor,
    fieldValueFunctionsContributor,
    predicateSnapFunctionsContributor,
    functionsSupporter,
    predicateSupporter
  )

  private val sortWrapperDeclarationOrder: Seq[PreambleContributor[Sort, _, _]] = Seq(
    sequencesContributor,
    setsContributor,
    multisetsContributor,
    domainsContributor,
    fieldValueFunctionsContributor,
    predicateSnapFunctionsContributor,
    functionsSupporter,
    predicateSupporter
  )

  private val symbolDeclarationOrder: Seq[PreambleContributor[_, _, _]] = Seq(
    /* Sequences depend on multisets ($Multiset.fromSeq, which is
     * additionally axiomatised in the sequences axioms).
     * Multisets depend on sets ($Multiset.fromSet).
     */
    setsContributor,
    multisetsContributor,
    sequencesContributor,
    domainsContributor,
    fieldValueFunctionsContributor,
    predicateSnapFunctionsContributor,
    functionsSupporter,
    predicateSupporter
  )

  private val axiomDeclarationOrder: Seq[PreambleContributor[Sort, _, _]] = Seq(
    sequencesContributor,
    setsContributor,
    multisetsContributor,
    domainsContributor,
    fieldValueFunctionsContributor,
    predicateSnapFunctionsContributor,
    functionsSupporter,
    predicateSupporter
  )

  private def analyzeProgramAndEmitPreambleContributions(program: ast.Program, sink: ProverLike) {
    analysisOrder foreach (component => {
      component.analyze(program)
      component.updateGlobalStateAfterAnalysis()
    })

    sink.comment("/" * 10 + " Sorts")
    sortDeclarationOrder foreach (component =>
      component.declareSortsAfterAnalysis(sink))

    sink.comment("/" * 10 + " Sort wrappers")
    emitSortWrappers(Seq(sorts.Int, sorts.Bool, sorts.Ref, sorts.Perm), sink)

    sortWrapperDeclarationOrder foreach (component =>
      emitSortWrappers(component.sortsAfterAnalysis, sink))

    sink.comment("/" * 10 + " Symbols")
    symbolDeclarationOrder foreach (component =>
      component.declareSymbolsAfterAnalysis(sink))

    sink.comment("/" * 10 + " Uniqueness assumptions from domains")
    domainsContributor.emitUniquenessAssumptionsAfterAnalysis(sink)

    /* Note: The triggers of the axioms of snapshot functions (FVFs and PSFs) mention the
     * corresponding sort wrappers. These axioms therefore need to be emitted after the sort
     * wrappers have been declared.
     */

    sink.comment("/" * 10 + " Axioms")
    axiomDeclarationOrder foreach (component =>
      component.emitAxiomsAfterAnalysis(sink))
  }

  private def emitSortWrappers(ss: Iterable[Sort], sink: ProverLike) {
    if (ss.nonEmpty) {
      sink.comment("Declaring additional sort wrappers")

      ss.foreach(sort => {
        val toSnapWrapper = terms.SortWrapperDecl(sort, sorts.Snap)
        val fromSnapWrapper = terms.SortWrapperDecl(sorts.Snap, sort)

        sink.declare(toSnapWrapper)
        sink.declare(fromSnapWrapper)

        preambleReader.emitParametricPreamble("/sortwrappers.smt2",
                                              Map("$S$" -> termConverter.convert(sort)),
                                              sink)
      })
    }
  }
}
