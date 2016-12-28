/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.verifier

import java.util.concurrent._
import org.apache.commons.pool2.impl.{DefaultPooledObject, GenericObjectPool, GenericObjectPoolConfig}
import org.apache.commons.pool2.{BasePooledObjectFactory, ObjectPool, PoolUtils, PooledObject}
import viper.silver.ast
import viper.silver.components.StatefulComponent
import viper.silicon._
import viper.silicon.decider.SMTLib2PreambleReader
import viper.silicon.utils
import viper.silicon.interfaces._
import viper.silicon.interfaces.decider.ProverLike
import viper.silicon.state._
import viper.silicon.state.terms.{Decl, Sort, Term, sorts}
import viper.silicon.supporters._
import viper.silicon.supporters.functions.FunctionSupporterProvider
import viper.silicon.supporters.qps._
import viper.silicon.verifier.BaseVerifier._

class MasterVerifier(config: Config)
    extends BaseVerifier(config, "00")
       with FunctionSupporterProvider[ST, H, S]
       with PredicateSupporterProvider[ST, H, S] {

  private val uniqueIdCounter = new utils.Counter(1)
  private def nextUniqueId(): String = f"${uniqueIdCounter.next()}%02d"

  protected val preambleReader = new SMTLib2PreambleReader

  protected val sequencesContributor = new DefaultSequencesContributor(preambleReader, symbolConverter, termConverter)
  protected val setsContributor = new DefaultSetsContributor(preambleReader, symbolConverter, termConverter)
  protected val multisetsContributor = new DefaultMultisetsContributor(preambleReader, symbolConverter, termConverter)
  protected val domainsContributor = new DefaultDomainsContributor(symbolConverter, domainTranslator)
  protected val fieldValueFunctionsContributor = new DefaultFieldValueFunctionsContributor(preambleReader, symbolConverter, termConverter, config)
  protected val predicateSnapFunctionsContributor = new DefaultPredicateSnapFunctionsContributor(preambleReader, symbolConverter, termConverter, predSnapGenerator, config)

  private val statefulSubcomponents = List[StatefulComponent](
    uniqueIdCounter,
    sequencesContributor, setsContributor, multisetsContributor, domainsContributor,
    fieldValueFunctionsContributor,
    predicateSnapFunctionsContributor,
    functionsSupporter, predicateSupporter
  )

  private val numberOfSlaveVerifiers: Int = config.numberOfParallelVerifiers()
  private var slaveVerifiers: Seq[SlaveVerifier] = Seq.empty
  private var slaveVerifierExecutor: ExecutorService = _
  private var slaveVerifierPool: ObjectPool[SlaveVerifier] = _

  private type VerificationTask = () => VerificationResult

  /* Lifetime */

  override def start() {
    super.start()
    statefulSubcomponents foreach (_.start())
    setupSlaveVerifierPool()
  }

  override def reset() {
    super.reset()
    statefulSubcomponents foreach (_.reset())
    resetSlaveVerifierPool()
  }

  override def stop() {
    super.stop()
    statefulSubcomponents foreach (_.stop())
    teardownSlaveVerifierPool()
  }

  /* Verifier orchestration */

  private object allProvers extends ProverLike {
    def emit(content: String): Unit = {
      decider.prover.emit(content)
      workerProvers.emit(content)
    }

    def assume(term: Term): Unit = {
      decider.prover.assume(term)
      workerProvers.assume(term)
    }

    def declare(decl: Decl): Unit = {
      decider.prover.declare(decl)
      workerProvers.declare(decl)
    }

    def comment(content: String): Unit = {
      decider.prover.comment(content)
      workerProvers.comment(content)
    }
  }

  private object workerProvers extends ProverLike {
    def emit(content: String): Unit = slaveVerifiers foreach (_.decider.prover.emit(content))
    def assume(term: Term): Unit = slaveVerifiers foreach (_.decider.prover.assume(term))
    def declare(decl: Decl): Unit =  slaveVerifiers foreach (_.decider.prover.declare(decl))
    def comment(content: String): Unit = slaveVerifiers foreach (_.decider.prover.comment(content))
  }

  /* Program verification */

  def verify(program: ast.Program): List[VerificationResult] = {
    predSnapGenerator.setup(program) // TODO: Why did Nadja put this here?


    allProvers.comment("Started: " + bookkeeper.formattedStartTime)
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
      val res = functionsSupporter.verify(function, createInitialContext(function, program))
      bookkeeper.functionVerified(function.name)
      res
    })

    val predicateVerificationResults = predicateSupporter.units.toList flatMap (predicate =>{
      val res = predicateSupporter.verify(predicate, createInitialContext(predicate, program))
      bookkeeper.predicateVerified(predicate.name)
      res
    })

    /* TODO: Ugly hack! The slaves' predicate supported currently doesn't generate its own
     *       predicate data (because it doesn't analyse the program under verification),
     *       but the data is also used when calling predicateSupporter.(un)fold
     */
    slaveVerifiers foreach (sv => {
      sv.predicateSupporter.program = predicateSupporter.program
      sv.predicateSupporter.predicateData = predicateSupporter.predicateData
    })

    decider.prover.stop()

    workerProvers.comment("-" * 60)
    workerProvers.comment("Begin function- and predicate-related preamble")
    predicateSupporter.declareSortsAfterVerification(workerProvers)
    functionsSupporter.declareSortsAfterVerification(workerProvers)
    predicateSupporter.declareSymbolsAfterVerification(workerProvers)
    functionsSupporter.declareSymbolsAfterVerification(workerProvers)
    predicateSupporter.emitAxiomsAfterVerification(workerProvers)
    functionsSupporter.emitAxiomsAfterVerification(workerProvers)
    workerProvers.comment("End function- and predicate-related preamble")
    workerProvers.comment("-" * 60)

    val verificationTaskFutures: Seq[Future[Seq[VerificationResult]]] =
      program.methods.filterNot(excludeMethod).map(method => {
        val c = createInitialContext(method, program)

        val verificationTask =
          new Callable[Seq[VerificationResult]] {
            def call(): Seq[VerificationResult] = {
              var slave: SlaveVerifier = null

              try {
                slave = slaveVerifierPool.borrowObject()

                val res = slave.methodSupporter.verify(method, c)
                bookkeeper.methodVerified(method.name)

                res
              } finally {
                if (slave != null) {
                  slaveVerifierPool.returnObject(slave)
                }
              }
            }
          }

        slaveVerifierExecutor.submit(verificationTask)
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

  private def createInitialContext(member: ast.Member, program: ast.Program): C = {
    val quantifiedFields = toSet(ast.utility.QuantifiedPermissions.quantifiedFields(member, program))
    val quantifiedPredicates = toSet(ast.utility.QuantifiedPermissions.quantifiedPredicates(member, program))
    val applyHeuristics = program.fields.exists(_.name.equalsIgnoreCase("__CONFIG_HEURISTICS"))

    DefaultContext[H](program = program,
                      qpFields = quantifiedFields,
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
      log.info(s"Additional Z3 configuration options are '${config.z3ConfigArgs()}'")
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
    analysisOrder foreach (component =>
      component.analyze(program))

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

  /* Slave verifier pooling */

  private def setupSlaveVerifierPool(): Unit = {
    val poolConfig: GenericObjectPoolConfig = new GenericObjectPoolConfig()
    poolConfig.setMaxTotal(numberOfSlaveVerifiers)
    poolConfig.setBlockWhenExhausted(true)

    val factory = PoolUtils.synchronizedPooledFactory(slaveVerifierPoolableObjectFactory)

    slaveVerifierPool =
  //    PoolUtils.synchronizedPool(
        new GenericObjectPool[SlaveVerifier](factory, poolConfig)
  //    )

    PoolUtils.prefill(slaveVerifierPool, poolConfig.getMaxTotal)
    //  Thread.sleep(2000)

    assert(slaveVerifiers.length == poolConfig.getMaxTotal)
    slaveVerifiers foreach (_.start())

    slaveVerifierExecutor = Executors.newFixedThreadPool(poolConfig.getMaxTotal)
  }

  private def resetSlaveVerifierPool(): Unit = {
    slaveVerifiers foreach (_.reset())
  }

  private def teardownSlaveVerifierPool(): Unit = {
    slaveVerifiers foreach (_.stop())

    slaveVerifierExecutor.shutdown()
    slaveVerifierExecutor.awaitTermination(10, TimeUnit.SECONDS)

    slaveVerifierPool.close()
  }

  private object slaveVerifierPoolableObjectFactory extends BasePooledObjectFactory[SlaveVerifier] {
    def create(): SlaveVerifier = {
      val slave = new SlaveVerifier(config, nextUniqueId())
      slaveVerifiers = slave +: slaveVerifiers

      slave
    }

    def wrap(arg: SlaveVerifier): PooledObject[SlaveVerifier] = new DefaultPooledObject(arg)
  }
}
