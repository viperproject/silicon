// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package viper.silicon.verifier

import viper.silicon.Config.ExhaleMode

import java.text.SimpleDateFormat
import java.util.concurrent._
import scala.annotation.unused
import scala.collection.mutable
import scala.util.Random
import viper.silver.ast
import viper.silver.components.StatefulComponent
import viper.silicon._
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.decider.SMTLib2PreambleReader
import viper.silicon.extensions.ConditionalPermissionRewriter
import viper.silicon.interfaces._
import viper.silicon.interfaces.decider.ProverLike
import viper.silicon.logger.{MemberSymbExLogger, SymbExLogger}
import viper.silicon.reporting.{MultiRunRecorders, condenseToViperResult}
import viper.silicon.state._
import viper.silicon.state.terms.{Decl, Sort, Term, sorts}
import viper.silicon.supporters._
import viper.silicon.supporters.functions.{DefaultFunctionVerificationUnitProvider, FunctionData}
import viper.silicon.supporters.qps._
import viper.silicon.utils.Counter
import viper.silver.ast.{BackendType, Member}
import viper.silver.ast.utility.rewriter.Traverse
import viper.silver.cfg.silver.SilverCfg
import viper.silver.reporter.{ConfigurationConfirmation, ExecutionTraceReport, Reporter, VerificationResultMessage, VerificationTerminationMessage, QuantifierChosenTriggersMessage, WarningsDuringTypechecking}
import viper.silver.verifier.TypecheckerWarning

/* TODO: Extract a suitable MainVerifier interface, probably including
 *         - def verificationPoolManager: VerificationPoolManager)
 *         - def uniqueIdCounter: String)
 */

trait MainVerifier extends Verifier {
  def nextUniqueVerifierId(): String
  def verificationPoolManager: VerificationPoolManager
  def rootSymbExLogger: SymbExLogger[_ <: MemberSymbExLogger]
}

class DefaultMainVerifier(config: Config,
                          override val reporter: Reporter,
                          override val rootSymbExLogger: SymbExLogger[_ <: MemberSymbExLogger])
    extends BaseVerifier(config, "00")
       with MainVerifier
       with DefaultFunctionVerificationUnitProvider
       with DefaultPredicateVerificationUnitProvider {

  Verifier.config = config

  private val uniqueIdCounter = new Counter(1)
  def nextUniqueVerifierId(): String = f"${uniqueIdCounter.next()}%02d"

  override def openSymbExLogger(member: Member): Unit = {
    symbExLog = rootSymbExLogger.openMemberScope(member, decider.pcs)
  }

  protected val preambleReader = new SMTLib2PreambleReader

  protected val sequencesContributor = new DefaultSequencesContributor(domainTranslator, config)
  protected val setsContributor = new DefaultSetsContributor(domainTranslator, config)
  protected val multisetsContributor = new DefaultMultisetsContributor(domainTranslator, config)
  protected val mapsContributor = new DefaultMapsContributor(domainTranslator, config)
  protected val domainsContributor = new DefaultDomainsContributor(symbolConverter, domainTranslator)
  protected val fieldValueFunctionsContributor = new DefaultFieldValueFunctionsContributor(preambleReader, symbolConverter, termConverter, config)
  protected val predSnapGenerator = new PredicateSnapGenerator(symbolConverter, snapshotSupporter)
  protected val predicateAndWandSnapFunctionsContributor = new DefaultPredicateAndWandSnapFunctionsContributor(preambleReader, termConverter, predSnapGenerator, config)

  private val _verificationPoolManager: VerificationPoolManager = new VerificationPoolManager(this)
  def verificationPoolManager: VerificationPoolManager = _verificationPoolManager

  private val statefulSubcomponents = List[StatefulComponent](
    uniqueIdCounter,
    sequencesContributor, setsContributor, multisetsContributor, mapsContributor, domainsContributor,
    fieldValueFunctionsContributor,
    predSnapGenerator, predicateAndWandSnapFunctionsContributor,
    functionsSupporter, predicateSupporter,
    _verificationPoolManager,
    MultiRunRecorders /* In lieu of a better place, include MultiRunRecorders singleton here */
  )

  /* Lifetime */

  override def start(): Unit = {
    super.start()
    statefulSubcomponents foreach (_.start())
  }

  override def reset(): Unit = {
    super.reset()
    statefulSubcomponents foreach (_.reset())
  }

  override def stop(): Unit = {
    super.stop()
    statefulSubcomponents foreach (_.stop())
  }

  def axiomsAfterAnalysis(): Iterable[Term] = this.domainsContributor.axiomsAfterAnalysis

  def postConditionAxioms(): Vector[Term] = functionsSupporter.getPostConditionAxioms()

  /* Verifier orchestration */

  private object allProvers extends ProverLike {
    def emit(content: String): Unit = {
      decider.prover.emit(content)
      _verificationPoolManager.pooledVerifiers.emit(content)
    }

    override def emit(contents: Iterable[String]): Unit = {
      decider.prover.emit(contents)
      _verificationPoolManager.pooledVerifiers.emit(contents)
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

    def saturate(timeout: Int, comment: String): Unit = {
      decider.prover.saturate(timeout, comment)
      _verificationPoolManager.pooledVerifiers.saturate(timeout, comment)
    }

    def saturate(data: Option[Config.ProverStateSaturationTimeout]): Unit = {
      decider.prover.saturate(data)
      _verificationPoolManager.pooledVerifiers.saturate(data)
    }

    override def emitSettings(contents: Iterable[String]): Unit = {
      decider.prover.emitSettings(contents)
      _verificationPoolManager.pooledVerifiers.emitSettings(contents)
    }
  }

  /* Program verification */

  def verify(originalProgram: ast.Program, cfgs: Seq[SilverCfg], inputFile: Option[String]): List[VerificationResult] = {
    /** Trigger computation is currently not thread-safe; hence, all triggers are computed
      * up-front, before the program is verified in parallel.
      * This is done bottom-up to ensure that nested quantifiers are transformed as well
      * (top-down should also work, but the default of 'innermost' won't).
      * See also [[viper.silicon.utils.ast.autoTrigger]].
      */
    var program: ast.Program =
      originalProgram.transform({
        case forall: ast.Forall if forall.isPure =>
          val res = viper.silicon.utils.ast.autoTrigger(forall, forall.autoTrigger)
          if (res.triggers.isEmpty)
            reporter.report(WarningsDuringTypechecking(Seq(TypecheckerWarning("No triggers provided or inferred for quantifier.", res.pos))))
          reporter report QuantifierChosenTriggersMessage(res, res.triggers)
          res
        case exists: ast.Exists =>
          val res = viper.silicon.utils.ast.autoTrigger(exists, exists.autoTrigger)
          if (res.triggers.isEmpty)
            reporter.report(WarningsDuringTypechecking(Seq(TypecheckerWarning("No triggers provided or inferred for quantifier.", res.pos))))
          reporter report QuantifierChosenTriggersMessage(res, res.triggers)
          res
      }, Traverse.BottomUp)

    // TODO: Autotrigger for cfgs.

    if (config.conditionalizePermissions()) {
      program = new ConditionalPermissionRewriter().rewrite(program).asInstanceOf[ast.Program]
    }

    if (config.printTranslatedProgram()) {
      println(program)
    }

    predSnapGenerator.setup(program) // TODO: Why did Nadja put this here?


    allProvers.comment("Started: " + new SimpleDateFormat("yyyy-MM-dd HH:mm:ss").format(System.currentTimeMillis()) /*bookkeeper.formattedStartTime*/)
    allProvers.comment("Silicon.version: " + Silicon.version)
    allProvers.comment(s"Input file: ${inputFile.getOrElse("<unknown>")}")
    allProvers.comment(s"Verifier id: $uniqueId")
    allProvers.comment("-" * 60)
    allProvers.comment("Begin preamble")

    allProvers.comment("/" * 10 + " Static preamble")
    emitStaticPreamble(allProvers)

    val (functionData, predicateData) = analyzeProgramAndEmitPreambleContributions(program, allProvers) // TODO: Add support for cfgs.

    allProvers.comment("End preamble")
    allProvers.comment("-" * 60)

    allProvers.saturate(config.proverSaturationTimeouts.afterPrelude)

    /* TODO: A workaround for Silver issue #94. toList must be before flatMap.
     *       Otherwise Set will be used internally and some error messages will be lost.
     */
    val functionVerificationResults = functionsSupporter.units.toList flatMap (function => {
      val startTime = System.currentTimeMillis()
      val results = functionsSupporter.verify(createInitialState(function, program, functionData, predicateData), function)
        .flatMap(extractAllVerificationResults)
      val elapsed = System.currentTimeMillis() - startTime
      reporter report VerificationResultMessage(s"silicon", function, elapsed, condenseToViperResult(results))
      logger debug s"Silicon finished verification of function `${function.name}` in ${viper.silver.reporter.format.formatMillisReadably(elapsed)} seconds with the following result: ${condenseToViperResult(results).toString}"
      setErrorScope(results, function)
    })

    val predicateVerificationResults = predicateSupporter.units.toList flatMap (predicate => {
      val startTime = System.currentTimeMillis()
      val results = predicateSupporter.verify(createInitialState(predicate, program, functionData, predicateData), predicate)
        .flatMap(extractAllVerificationResults)
      val elapsed = System.currentTimeMillis() - startTime
      reporter report VerificationResultMessage(s"silicon", predicate, elapsed, condenseToViperResult(results))
      logger debug s"Silicon finished verification of predicate `${predicate.name}` in ${viper.silver.reporter.format.formatMillisReadably(elapsed)} seconds with the following result: ${condenseToViperResult(results).toString}"
      setErrorScope(results, predicate)
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

        val s = createInitialState(method, program, functionData, predicateData).copy(parallelizeBranches =
          Verifier.config.parallelizeBranches()) /* [BRANCH-PARALLELISATION] */

        _verificationPoolManager.queueVerificationTask(v => {
          val startTime = System.currentTimeMillis()
          val results = v.methodSupporter.verify(s, method)
            .flatMap(extractAllVerificationResults)
          val elapsed = System.currentTimeMillis() - startTime

          reporter report VerificationResultMessage(s"silicon", method, elapsed, condenseToViperResult(results))
          logger debug s"Silicon finished verification of method `${method.name}` in ${viper.silver.reporter.format.formatMillisReadably(elapsed)} seconds with the following result: ${condenseToViperResult(results).toString}"

          setErrorScope(results, method)
        })
      }) ++ cfgs.map(cfg => {
        val s = createInitialState(cfg, program, functionData, predicateData).copy(parallelizeBranches = true) /* [BRANCH-PARALLELISATION] */

        _verificationPoolManager.queueVerificationTask(v => {
          val startTime = System.currentTimeMillis()
          val results = v.cfgSupporter.verify(s, cfg)
            .flatMap(extractAllVerificationResults)
          val elapsed = System.currentTimeMillis() - startTime

          reporter report VerificationResultMessage(s"silicon"/*, cfg*/, elapsed, condenseToViperResult(results))
          logger debug s"Silicon finished verification of method `CFG` in ${viper.silver.reporter.format.formatMillisReadably(elapsed)} seconds with the following result: ${condenseToViperResult(results).toString}"

          results
        })
      })

    val methodVerificationResults = verificationTaskFutures.flatMap(_.get())

    if (config.ideModeAdvanced()) {
      reporter report ExecutionTraceReport(
        rootSymbExLogger.logs.toIndexedSeq,
        this.axiomsAfterAnalysis().toList,
        this.postConditionAxioms().toList)
    }
    reporter report VerificationTerminationMessage()

    (   functionVerificationResults
     ++ predicateVerificationResults
     ++ methodVerificationResults)
  }

  private def createInitialState(member: ast.Member,
                                 program: ast.Program,
                                 functionData: Map[ast.Function, FunctionData],
                                 predicateData: Map[ast.Predicate, PredicateData]): State = {
    val quantifiedFields = InsertionOrderedSet(ast.utility.QuantifiedPermissions.quantifiedFields(member, program))
    val quantifiedPredicates = InsertionOrderedSet(ast.utility.QuantifiedPermissions.quantifiedPredicates(member, program))
    val quantifiedMagicWands = InsertionOrderedSet(ast.utility.QuantifiedPermissions.quantifiedMagicWands(member, program)).map(MagicWandIdentifier(_, program))
    val resourceTriggers: InsertionOrderedSet[Any] = InsertionOrderedSet(ast.utility.QuantifiedPermissions.resourceTriggers(member, program)).map{
      case wand: ast.MagicWand => MagicWandIdentifier(wand, program)
      case r => r
    }

    State(program = program,
          functionData = functionData,
          predicateData = predicateData,
          qpFields = quantifiedFields,
          qpPredicates = quantifiedPredicates,
          qpMagicWands = quantifiedMagicWands,
          predicateSnapMap = predSnapGenerator.snapMap,
          predicateFormalVarMap = predSnapGenerator.formalVarMap,
          currentMember = Some(member),
          heapDependentTriggers = resourceTriggers,
          moreCompleteExhale = Verifier.config.exhaleMode == ExhaleMode.MoreComplete)
  }

  private def createInitialState(@unused cfg: SilverCfg,
                                 program: ast.Program,
                                 functionData: Map[ast.Function, FunctionData],
                                 predicateData: Map[ast.Predicate, PredicateData]): State = {
    val quantifiedFields = InsertionOrderedSet(program.fields)
    val quantifiedPredicates = InsertionOrderedSet(program.predicates)
    val quantifiedMagicWands = InsertionOrderedSet[MagicWandIdentifier]() // TODO: Implement support for quantified magic wands.

    State(
      program = program,
      currentMember = None,
      functionData = functionData,
      predicateData = predicateData,
      qpFields = quantifiedFields,
      qpPredicates = quantifiedPredicates,
      qpMagicWands = quantifiedMagicWands,
      predicateSnapMap = predSnapGenerator.snapMap,
      predicateFormalVarMap = predSnapGenerator.formalVarMap,
      moreCompleteExhale = Verifier.config.exhaleMode == ExhaleMode.MoreComplete)
  }

  private def excludeMethod(method: ast.Method) = (
       !method.name.matches(config.includeMethods())
    || method.name.matches(config.excludeMethods()))

  /* Prover preamble: Static preamble */

  private def emitStaticPreamble(sink: ProverLike): Unit = {
    sink.comment(s"\n; ${decider.prover.staticPreamble}")
    preambleReader.emitPreamble(decider.prover.staticPreamble, sink, true)

    if (config.proverRandomizeSeeds) {
      sink.comment(s"\n; Randomise seeds [--${config.rawProverRandomizeSeeds.name}]")
      val options = decider.prover.randomizeSeedsOptions
        .map (key => s"(set-option :$key ${Random.nextInt(10000)})")

      preambleReader.emitPreamble(options, sink, true)
    }

    val smt2ConfigOptions =
      config.proverConfigArgs.map { case (k, v) => s"(set-option :$k $v)" }

    if (smt2ConfigOptions.nonEmpty) {
      // One can pass options to the prover. This allows to check whether they have been received.
      val msg = s"Additional prover configuration options are '${config.proverConfigArgs}'"
      reporter report ConfigurationConfirmation(msg)
      logger info msg
      preambleReader.emitPreamble(smt2ConfigOptions, sink, true)
    }

    sink.comment("\n; /preamble.smt2")
    preambleReader.emitPreamble("/preamble.smt2", sink, false)
  }

  /* Prover preamble: After program analysis */

  private val analysisOrder: Seq[PreambleContributor[_, _, _]] = Seq(
    sequencesContributor,
    setsContributor,
    multisetsContributor,
    mapsContributor,
    domainsContributor,
    fieldValueFunctionsContributor,
    predicateAndWandSnapFunctionsContributor,
    functionsSupporter,
    predicateSupporter
  )

  private val sortDeclarationOrder: Seq[PreambleContributor[_, _, _]] = Seq(
    sequencesContributor,
    setsContributor,
    multisetsContributor,
    mapsContributor,
    domainsContributor,
    fieldValueFunctionsContributor,
    predicateAndWandSnapFunctionsContributor,
    functionsSupporter,
    predicateSupporter
  )

  private val sortWrapperDeclarationOrder: Seq[PreambleContributor[Sort, _, _]] = Seq(
    sequencesContributor,
    setsContributor,
    multisetsContributor,
    mapsContributor,
    domainsContributor,
    fieldValueFunctionsContributor,
    predicateAndWandSnapFunctionsContributor,
    functionsSupporter,
    predicateSupporter
  )

  private val symbolDeclarationOrder: Seq[PreambleContributor[_, _, _]] = Seq(
    /* Sequences depend on multisets ($Multiset.fromSeq, which is
     * additionally axiomatised in the sequences axioms).
     * Multisets depend on sets ($Multiset.fromSet).
     * Maps depend on sets (Map_domain, Map_range, Map_cardinality).
     */
    setsContributor,
    multisetsContributor,
    sequencesContributor,
    mapsContributor,
    domainsContributor,
    fieldValueFunctionsContributor,
    predicateAndWandSnapFunctionsContributor,
    functionsSupporter,
    predicateSupporter
  )

  private val axiomDeclarationOrder: Seq[PreambleContributor[Sort, _, _]] = Seq(
    sequencesContributor,
    setsContributor,
    multisetsContributor,
    mapsContributor,
    domainsContributor,
    fieldValueFunctionsContributor,
    predicateAndWandSnapFunctionsContributor,
    functionsSupporter,
    predicateSupporter
  )

  private def analyzeProgramAndEmitPreambleContributions(program: ast.Program, sink: ProverLike) = {
    analysisOrder foreach (component => {
      component.analyze(program)
    })
    val predicateData = predicateSupporter.predicateData
    val functionData = functionsSupporter.functionData
    functionsSupporter.predicateData = predicateData

    sink.comment("/" * 10 + " Sorts")
    sortDeclarationOrder foreach (component =>
      component.declareSortsAfterAnalysis(sink))

    sink.comment("/" * 10 + " Sort wrappers")
    emitSortWrappers(Seq(sorts.Int, sorts.Bool, sorts.Ref, sorts.Perm), sink)

    sortWrapperDeclarationOrder foreach (component =>
      emitSortWrappers(component.sortsAfterAnalysis, sink))

    val backendTypes = new mutable.LinkedHashSet[BackendType]
    program.visit{
      case t: BackendType => backendTypes.add(t)
    }
    emitSortWrappers(backendTypes map symbolConverter.toSort, sink)

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

    (functionData, predicateData)
  }

  private def emitSortWrappers(ss: Iterable[Sort], sink: ProverLike): Unit = {
    if (ss.nonEmpty) {
      sink.comment("Declaring additional sort wrappers")

      ss.foreach(sort => {
        val toSnapWrapper = terms.SortWrapperDecl(sort, sorts.Snap)
        val fromSnapWrapper = terms.SortWrapperDecl(sorts.Snap, sort)

        sink.declare(toSnapWrapper)
        sink.declare(fromSnapWrapper)

        val sanitizedSortString = termConverter.convertSanitized(sort)
        val sortString = termConverter.convert(sort)

        if (sanitizedSortString.contains("$T$")) {
          // Ensure that sanitizedSortString does not contain the key which we substitute with sortString,
          // because otherwise, we can have $T$ -> ....$S$.... -> ....<sortString>...., which is not what we want.
          var i = 0
          while (sanitizedSortString.contains(s"$$T$i$$")) {
            i += 1
          }

          preambleReader.emitParametricPreamble("/sortwrappers.smt2",
            Map("$T$" -> s"$$T$i$$",
                "$S$" -> sanitizedSortString,
                s"$$T$i$$" -> sortString),
            sink)
        } else {
          preambleReader.emitParametricPreamble("/sortwrappers.smt2",
            Map("$S$" -> sanitizedSortString,
                "$T$" -> sortString),
            sink)
        }

      })
    }
  }

  private def setErrorScope(results: Seq[VerificationResult], scope: Member): Seq[VerificationResult] = {
    results.foreach {
      case f: Failure => f.message.scope = Some(scope)
      case _ =>
    }
    results
  }

  /**
    * In case Silicon encounters an expected error (i.e. `ErrorMessage.isExpected`), Silicon continues (until at most
    * config.numberOfErrorsToReport() have been encountered (per member)).
    * This function combines the verification result with verification results stored in its `previous` field.
    */
  private def extractAllVerificationResults(res: VerificationResult): Seq[VerificationResult] =
    res :: res.previous.toList
}
