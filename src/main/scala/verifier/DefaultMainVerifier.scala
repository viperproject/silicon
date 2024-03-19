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
import viper.silicon.state.terms.{ConstDecl, Decl, Sort, Term, sorts}
import viper.silicon.supporters._
import viper.silicon.supporters.functions.{DefaultFunctionVerificationUnitProvider, FunctionData}
import viper.silicon.supporters.qps._
import viper.silicon.utils.Counter
import viper.silver.ast.{BackendType, Member}
import viper.silver.ast.utility.rewriter.Traverse
import viper.silver.cfg.silver.SilverCfg
import viper.silver.reporter.{AnnotationWarning, ConfigurationConfirmation, ExecutionTraceReport, QuantifierChosenTriggersMessage, Reporter, VerificationResultMessage, VerificationTerminationMessage, WarningsDuringVerification}
import viper.silver.verifier.VerifierWarning

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
       with DefaultPredicateVerificationUnitProvider{

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
    predicateSupporter,
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

    override def setOption(name: String, value: String): String = {
      decider.prover.setOption(name, value)
      _verificationPoolManager.pooledVerifiers.setOption(name, value)
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
            reporter.report(WarningsDuringVerification(Seq(VerifierWarning("No triggers provided or inferred for quantifier.", res.pos))))
          reporter report QuantifierChosenTriggersMessage(res, res.triggers, forall.triggers)
          res
        case exists: ast.Exists =>
          val res = viper.silicon.utils.ast.autoTrigger(exists, exists.autoTrigger)
          if (res.triggers.isEmpty)
            reporter.report(WarningsDuringVerification(Seq(VerifierWarning("No triggers provided or inferred for quantifier.", res.pos))))
          reporter report QuantifierChosenTriggersMessage(res, res.triggers, exists.triggers)
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

    _verificationPoolManager.pooledVerifiers.push()
    val supporters = _verificationPoolManager.workerVerifiers.map(_.functionsSupporter)
    var allEmittedFunctionAxioms: Vector[Term] = Vector.empty
    // NOTE: same functionData map for all
    supporters.foreach(s => s.functionData = functionsSupporter.functionData)

    val units = functionsSupporter.unitsByLevel
    val allResults = units.map(funcs => {
      val levelResultFutures = funcs.map(f => {
        _verificationPoolManager.queueVerificationTask(v => {
          val startTime = System.currentTimeMillis()
          val results = v.functionsSupporter.verify(createInitialState(f, program, functionsSupporter.functionData, predicateData), f)
          val elapsed = System.currentTimeMillis() - startTime
          reporter report VerificationResultMessage(s"silicon", f, elapsed, condenseToViperResult(results))
          val msg = s"Silicon finished verification of function `${f.name}` in ${viper.silver.reporter.format.formatMillisReadably(elapsed)} seconds with the following result: ${condenseToViperResult(results).toString}"
          logger debug msg
          (setErrorScope(results, f), v.functionsSupporter.functionData(f), f, v)
        })
      })
      val levelResults = levelResultFutures.map(_.get())
      val results = levelResults.map(_._1)
      // NOTE: some functionsupporters have been used (some possibly more than once)

      val formalArgs = levelResults.map(r => (r._4, r._2.formalArgs.values.map(ConstDecl(_)).toSeq :+ ConstDecl(r._2.formalResult)))
      val axioms = levelResults.map(r => (r._4, Seq(r._2.limitedAxiom, r._2.triggerAxiom) ++ r._2.postAxiom ++ r._2.postPreconditionPropagationAxiom ++
        (if (r._3.body.isDefined && r._2.verificationFailures.isEmpty) r._2.definitionalAxiom ++ r._2.bodyPreconditionPropagationAxiom else Seq())))
      allEmittedFunctionAxioms ++= axioms.unzip._2.flatten

      val freshFunctions = _verificationPoolManager.workerVerifiers.map(v => (v, v.decider.getAndDeleteFreshFunctions()))
      val freshMacros = _verificationPoolManager.workerVerifiers.map(v => (v, v.decider.getAndDeleteFreshMacros()))

      // NOTE: update functionData field with new/updated functon data objects
      val newData = levelResults.map(t => t._3 -> t._2)
      functionsSupporter.functionData ++= newData


      _verificationPoolManager.workerVerifiers.foreach(s => {
        s.functionsSupporter.functionData ++= newData
        formalArgs.foreach{case (v, decls) => {
          if (v != s){
            decls.foreach(s.decider.prover.declare(_))
          }
        }}
        freshFunctions.foreach{case (v, ff) => {
          if (v != s){
            ff.foreach(s.decider.prover.declare(_))
          }
        }}
        freshMacros.foreach{case (v, fm) => {
          if (v != s){
            fm.foreach(s.decider.prover.declare(_))
          }
        }}
        axioms.foreach{case (v, axs) => {
          if (v != s){
            s.functionsSupporter.emitAndRecordFunctionAxioms(axs: _*)
          }
        }}
      })
      results.flatten
    })


    val functionVerificationResults = allResults.flatten.toList

    _verificationPoolManager.pooledVerifiers.pop()
    allEmittedFunctionAxioms foreach _verificationPoolManager.pooledVerifiers.assume
    _verificationPoolManager.pooledVerifiers.push()

    val predicateVerificationFutures = predicateSupporter.units.toList map (predicate => {
      _verificationPoolManager.queueVerificationTask(v => {
        val startTime = System.currentTimeMillis()
        val results = v.predicateSupporter.verify(createInitialState(predicate, program, functionsSupporter.functionData, predicateData), predicate)
        val elapsed = System.currentTimeMillis() - startTime
        reporter report VerificationResultMessage(s"silicon", predicate, elapsed, condenseToViperResult(results))
        val msg = s"Silicon finished verification of predicate `${predicate.name}` in ${viper.silver.reporter.format.formatMillisReadably(elapsed)} seconds with the following result: ${condenseToViperResult(results).toString}"
        logger debug msg
        setErrorScope(results, predicate)
      })
    })

    val predicateVerificationResults = predicateVerificationFutures.map(_.get()).flatten

    _verificationPoolManager.pooledVerifiers.pop()

    decider.prover.stop()

    _verificationPoolManager.pooledVerifiers.comment("-" * 60)
    _verificationPoolManager.pooledVerifiers.comment("Begin function- and predicate-related preamble")
    //predicateSupporter.declareSortsAfterVerification(_verificationPoolManager.pooledVerifiers)
    //functionsSupporter.declareSortsAfterVerification(_verificationPoolManager.pooledVerifiers)
    //predicateSupporter.declareSymbolsAfterVerification(_verificationPoolManager.pooledVerifiers)
    //functionsSupporter.declareSymbolsAfterVerification(_verificationPoolManager.pooledVerifiers)
    //predicateSupporter.emitAxiomsAfterVerification(_verificationPoolManager.pooledVerifiers)
    //allEmittedFunctionAxioms foreach _verificationPoolManager.pooledVerifiers.assume
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

    val mce = member.info.getUniqueInfo[ast.AnnotationInfo] match {
      case Some(ai) if ai.values.contains("exhaleMode") =>
        ai.values("exhaleMode") match {
          case Seq("0") | Seq("greedy") | Seq("2") | Seq("mceOnDemand") =>
            if (Verifier.config.counterexample.isSupplied)
              reporter report AnnotationWarning(s"Member ${member.name} has exhaleMode annotation that may interfere with counterexample generation.")
            false
          case Seq("1") | Seq("mce") | Seq("moreCompleteExhale") => true
          case v =>
            reporter report AnnotationWarning(s"Member ${member.name} has invalid exhaleMode annotation value $v. Annotation will be ignored.")
            Verifier.config.exhaleMode == ExhaleMode.MoreComplete
        }
      case _ => Verifier.config.exhaleMode == ExhaleMode.MoreComplete
    }
    val moreJoinsAnnotated = member.info.getUniqueInfo[ast.AnnotationInfo] match {
      case Some(ai) => ai.values.contains("moreJoins")
      case _ => false
    }
    val moreJoins = (Verifier.config.moreJoins() || moreJoinsAnnotated) && member.isInstanceOf[ast.Method]

    val methodPermCache = mutable.HashMap[String, InsertionOrderedSet[ast.Location]]()
    val permResources: InsertionOrderedSet[ast.Location] = if (Verifier.config.unsafeWildcardOptimization()) member match {
      case m: ast.Method if m.body.isDefined =>
        val bodyResources: Iterable[InsertionOrderedSet[ast.Location]] = m.body.get.collect {
          case ast.CurrentPerm(la: ast.LocationAccess) => InsertionOrderedSet(la.loc(program))
          case ast.MethodCall(name, _, _) =>
            if (methodPermCache.contains(name))
              methodPermCache(name)
            else {
              val calledMethod = program.findMethod(name)
              val preResources: Seq[ast.Location] = calledMethod.pres.flatMap(pre => pre.whenExhaling.collect {
                case ast.CurrentPerm(la: ast.LocationAccess) => la.loc(program)
              })
              val postResources: Seq[ast.Location] = calledMethod.posts.flatMap(post => post.whenInhaling.collect {
                case ast.CurrentPerm(la: ast.LocationAccess) => la.loc(program)
              })
              val all = InsertionOrderedSet(preResources ++ postResources)
              methodPermCache.update(name, all)
              all
            }
        }
        val preResources: Seq[ast.Location] = m.pres.flatMap(pre => pre.whenInhaling.collect {
          case ast.CurrentPerm(la: ast.LocationAccess) => la.loc(program)
        })
        val postResources: Seq[ast.Location] = m.posts.flatMap(post => post.whenExhaling.collect {
          case ast.CurrentPerm(la: ast.LocationAccess) => la.loc(program)
        })
        InsertionOrderedSet(bodyResources.flatten ++ preResources ++ postResources)
      case _ => InsertionOrderedSet.empty
    } else InsertionOrderedSet.empty

    State(program = program,
          functionData = functionData,
          predicateData = predicateData,
          qpFields = quantifiedFields,
          qpPredicates = quantifiedPredicates,
          qpMagicWands = quantifiedMagicWands,
          permLocations = permResources,
          predicateSnapMap = predSnapGenerator.snapMap,
          predicateFormalVarMap = predSnapGenerator.formalVarMap,
          currentMember = Some(member),
          heapDependentTriggers = resourceTriggers,
          moreCompleteExhale = mce,
          moreJoins = moreJoins)
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
      moreCompleteExhale = Verifier.config.exhaleMode == ExhaleMode.MoreComplete,
      moreJoins = Verifier.config.moreJoins())
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
