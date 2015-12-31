/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon

import org.slf4s.Logging
import viper.silver.ast
import viper.silver.components.StatefulComponent
import viper.silver.verifier.errors.{ContractNotWellformed, PostconditionViolated}
import viper.silicon.interfaces._
import viper.silicon.interfaces.decider.Decider
import viper.silicon.interfaces.state._
import viper.silicon.interfaces.state.factoryUtils.Ø
import viper.silicon.decider.{DeciderProvider, SMTLib2PreambleEmitter}
import viper.silicon.state._
import viper.silicon.state.terms.{AxiomRewriter, sorts, Sort}
import viper.silicon.supporters._
import viper.silicon.supporters.functions.FunctionSupporterProvider
import viper.silicon.supporters.qps._
import viper.silicon.reporting.{DefaultStateFormatter, Bookkeeper}
import viper.silicon.utils.NoOpStatefulComponent

/* TODO: 1. Extract method verification code into a MethodSupporter
 *       2. Remove this trait
 */
trait AbstractElementVerifier[ST <: Store[ST],
                             H <: Heap[H], PC <: PathConditions[PC],
                             S <: State[ST, H, S]]
    extends Logging
       with Evaluator[ST, H, S, DefaultContext[H]]
       with Producer[ST, H, S, DefaultContext[H]]
       with Consumer[ST, H, S, DefaultContext[H]]
       with Executor[ST, H, S, DefaultContext[H]]
   { this: MagicWandSupporter[ST, H, PC, S] =>

  private[this] type C = DefaultContext[H]

  protected val config: Config
  protected val decider: Decider[ST, H, PC, S, C]
  protected val stateFactory: StateFactory[ST, H, S]
  protected val stateFormatter: StateFormatter[ST, H, S, String]
  protected val symbolConverter: SymbolConvert
  protected val quantifiedChunkSupporter: QuantifiedChunkSupporter[ST, H, PC, S, C]

  import decider.{fresh, inScope}
  import stateFactory._

  def createInitialContext(member: ast.Member, program: ast.Program): DefaultContext[H] = {
    val quantifiedFields = toSet(ast.utility.QuantifiedPermissions.quantifiedFields(member, program))
    val applyHeuristics = program.fields.exists(_.name.equalsIgnoreCase("__CONFIG_HEURISTICS"))

    DefaultContext[H](program = program,
                      qpFields = quantifiedFields,
                      applyHeuristics = applyHeuristics)
  }

  def verify(method: ast.Method, c: C): VerificationResult = {
    log.debug("\n\n" + "-" * 10 + " METHOD " + method.name + "-" * 10 + "\n")
    decider.prover.logComment("%s %s %s".format("-" * 10, method.name, "-" * 10))

    val ins = method.formalArgs.map(_.localVar)
    val outs = method.formalReturns.map(_.localVar)

    val γ = Γ(   ins.map(v => (v, fresh(v)))
              ++ outs.map(v => (v, fresh(v)))
              ++ method.locals.map(_.localVar).map(v => (v, fresh(v))))

    val σ = Σ(γ, Ø, Ø)

    val pres = method.pres
    val posts = method.posts
    val body = method.body.toCfg

    val postViolated = (offendingNode: ast.Exp) => PostconditionViolated(offendingNode, method)

    /* Combined the well-formedness check and the execution of the body, which are two separate
     * rules in Smans' paper.
     */
    inScope {
      produces(σ, fresh, terms.FullPerm(), pres, ContractNotWellformed, c)((σ1, c2) => {
        val σ2 = σ1 \ (γ = σ1.γ, h = Ø, g = σ1.h)
           (inScope {
              /* TODO: Checking self-framingness here fails if pold(e) reads a location
               *       to which access is not required by the precondition.
               */
              magicWandSupporter.checkWandsAreSelfFraming(σ1.γ, σ1.h, method, c2)}
        && inScope {
              produces(σ2, fresh, terms.FullPerm(), posts, ContractNotWellformed, c2)((_, c3) =>
                Success())}
        && inScope {
              exec(σ1 \ (g = σ1.h), body, c2)((σ2, c3) =>
                consumes(σ2, terms.FullPerm(), posts, postViolated, c3)((σ3, _, c4) =>
                  Success()))})})}
  }
}

class DefaultElementVerifier[ST <: Store[ST],
                             H <: Heap[H],
                             PC <: PathConditions[PC],
                             S <: State[ST, H, S]]
    (val config: Config,
     val stateFactory: StateFactory[ST, H, S],
     val pathConditionsFactory: PathConditionsFactory[PC],
     val symbolConverter: SymbolConvert,
     val stateFormatter: StateFormatter[ST, H, S, String],
     val bookkeeper: Bookkeeper,
     val identifierFactory: IdentifierFactory,
     val axiomRewriter: AxiomRewriter)
    (protected implicit val manifestH: Manifest[H])
    extends NoOpStatefulComponent
       with AbstractElementVerifier[ST, H, PC, S]
       with DeciderProvider[ST, H, PC, S]
       with DefaultEvaluator[ST, H, PC, S]
       with DefaultProducer[ST, H, PC, S]
       with DefaultConsumer[ST, H, PC, S]
       with DefaultExecutor[ST, H, PC, S]
       with FunctionSupporterProvider[ST, H, PC, S]
       with ChunkSupporterProvider[ST, H, PC, S]
       with PredicateSupporterProvider[ST, H, PC, S]
       with DefaultBrancher[ST, H, PC, S]
       with DefaultJoiner[ST, H, PC, S]
       with DefaultLetHandler[ST, H, S, DefaultContext[H]]
       with MagicWandSupporter[ST, H, PC, S]
       with HeuristicsSupporter[ST, H, PC, S]
       with HeapCompressorProvider[ST, H, PC, S, DefaultContext[H]]
       with QuantifiedChunkSupporterProvider[ST, H, PC, S]
       with Logging

class DefaultVerifier(val config: Config)
    extends StatefulComponent
       with Logging {

  private type ST = MapBackedStore
  private type H = ListBackedHeap
  private type PC = MutableSetBackedPathConditions
  private type S = DefaultState[ST, H]
  private type C = DefaultContext[H]

  val bookkeeper = new Bookkeeper(config)
  val stateFormatter = new DefaultStateFormatter[ST, H, S](config)
  val pathConditionsFactory = new DefaultPathConditionsFactory()
  val symbolConverter = new DefaultSymbolConvert()
  val domainTranslator = new DefaultDomainsTranslator(symbolConverter)
  val stateFactory = new DefaultStateFactory()
  val identifierFactory = new DefaultIdentifierFactory
  val axiomRewriter = new AxiomRewriter(new utils.Counter(), bookkeeper.logfiles("axiomRewriter"))

  val ev =
    new DefaultElementVerifier(config, stateFactory, pathConditionsFactory, symbolConverter,
                               stateFormatter, bookkeeper, identifierFactory, axiomRewriter)

  val decider = ev.decider

  val preambleEmitter = new SMTLib2PreambleEmitter(decider.prover)
  val sequencesEmitter = new DefaultSequencesEmitter(decider.prover, symbolConverter, preambleEmitter)
  val setsEmitter = new DefaultSetsEmitter(decider.prover, symbolConverter, preambleEmitter)
  val multisetsEmitter = new DefaultMultisetsEmitter(decider.prover, symbolConverter, preambleEmitter)
  val domainsEmitter = new DefaultDomainsEmitter(decider.prover, domainTranslator, symbolConverter)
  val fieldValueFunctionsEmitter = new DefaultFieldValueFunctionsEmitter(decider.prover, symbolConverter, preambleEmitter)

  private val statefulSubcomponents = List[StatefulComponent](
    bookkeeper,
    preambleEmitter, sequencesEmitter, setsEmitter, multisetsEmitter, domainsEmitter,
    fieldValueFunctionsEmitter,
    decider, identifierFactory,
    ev,
    ev.functionsSupporter, ev.predicateSupporter, ev.quantifiedChunkSupporter)

  /* Lifetime */

  override def start() {
    statefulSubcomponents foreach (_.start())
  }

  override def reset() {
    statefulSubcomponents foreach (_.reset())
  }

  override def stop() {
    statefulSubcomponents foreach (_.stop())
  }

  /* Program verification */

  def verify(program: ast.Program): List[VerificationResult] = {
    emitPreamble(program)

//    ev.predicateSupporter.handlePredicates(program)

    /* FIXME: A workaround for Silver issue #94.
     * toList must be before flatMap. Otherwise Set will be used internally and some
     * error messages will be lost.
     */
    val functionVerificationResults = ev.functionsSupporter.units.toList flatMap (function =>
      ev.functionsSupporter.verify(function, ev.createInitialContext(function, program)))

    val predicateVerificationResults = ev.predicateSupporter.units.toList flatMap (predicate =>
      ev.predicateSupporter.verify(predicate, ev.createInitialContext(predicate, program)))

    /* Fields and domains don't need to be verified */
    val methods = program.members.collect { case m: ast.Method => m }

    val methodVerificationResults = methods map (method => {
      val c = ev.createInitialContext(method, program)
//      ev.quantifiedChunkSupporter.initLastFVF(c.qpFields) /* TODO: Implement properly */

      ev.verify(method, c)
    })

    (   functionVerificationResults
     ++ predicateVerificationResults
     ++ methodVerificationResults)
  }

  private def filter(str: String) = (
       !str.matches(config.includeMembers())
    || str.matches(config.excludeMembers()))

  /* Prover preamble */

  private def emitPreamble(program: ast.Program) {
    decider.prover.logComment("Started: " + bookkeeper.formattedStartTime)
    decider.prover.logComment("Silicon.buildVersion: " + Silicon.buildVersion)

    decider.prover.logComment("-" * 60)
    decider.prover.logComment("Preamble start")

    sequencesEmitter.analyze(program)
    setsEmitter.analyze(program)
    multisetsEmitter.analyze(program)
    domainsEmitter.analyze(program)
    fieldValueFunctionsEmitter.analyze(program)
    ev.functionsSupporter.analyze(program)
    ev.predicateSupporter.analyze(program)

    emitStaticPreamble()

    sequencesEmitter.declareSorts()
    setsEmitter.declareSorts()
    multisetsEmitter.declareSorts()
    domainsEmitter.declareSorts()
    fieldValueFunctionsEmitter.declareSorts()
    ev.functionsSupporter.declareSorts()
    ev.predicateSupporter.declareSorts()

    /* Sequences depend on multisets ($Multiset.fromSeq, which is
     * additionally axiomatised in the sequences axioms).
     * Multisets depend on sets ($Multiset.fromSet).
     */
    setsEmitter.declareSymbols()
    multisetsEmitter.declareSymbols()
    sequencesEmitter.declareSymbols()
    domainsEmitter.declareSymbols()
    domainsEmitter.emitUniquenessAssumptions()
    fieldValueFunctionsEmitter.declareSymbols()
    ev.functionsSupporter.declareSymbols()
    ev.predicateSupporter.declareSymbols()

    sequencesEmitter.emitAxioms()
    setsEmitter.emitAxioms()
    multisetsEmitter.emitAxioms()
    domainsEmitter.emitAxioms()
    ev.functionsSupporter.emitAxioms()
    ev.predicateSupporter.emitAxioms()

    emitSortWrappers(Set(sorts.Int, sorts.Bool, sorts.Ref, sorts.Perm))
    emitSortWrappers(sequencesEmitter.sorts)
    emitSortWrappers(setsEmitter.sorts)
    emitSortWrappers(multisetsEmitter.sorts)
    emitSortWrappers(domainsEmitter.sorts)
    emitSortWrappers(fieldValueFunctionsEmitter.sorts)
    emitSortWrappers(ev.functionsSupporter.sorts)
    emitSortWrappers(ev.predicateSupporter.sorts)

    /* ATTENTION: The triggers mention the sort wrappers introduced for FVFs.
     * The axiom therefore needs to be emitted after the sort wrappers have
     * been emitted.
     */
    fieldValueFunctionsEmitter.emitAxioms()

    decider.prover.logComment("Preamble end")
    decider.prover.logComment("-" * 60)
  }

  private def emitSortWrappers(ss: Set[Sort]) {
    if (ss.nonEmpty) {
      decider.prover.logComment("Declaring additional sort wrappers")

      ss.foreach(sort => {
        val toSnapWrapper = terms.SortWrapperDecl(sort, sorts.Snap)
        val fromSnapWrapper = terms.SortWrapperDecl(sorts.Snap, sort)

        decider.prover.declare(toSnapWrapper)
        decider.prover.declare(fromSnapWrapper)

        preambleEmitter.emitParametricAssertions("/sortwrappers.smt2",
                                                 Map("$S$" -> decider.prover.termConverter.convert(sort)))
      })
    }
  }

  private def emitStaticPreamble() {
    decider.prover.logComment("\n; /z3config.smt2")
    preambleEmitter.emitPreamble("/z3config.smt2")

    val smt2ConfigOptions =
      config.z3ConfigArgs().map{case (k, v) => s"(set-option :$k $v)"}

    if (smt2ConfigOptions.nonEmpty) {
      log.info(s"Additional Z3 configuration options are '${config.z3ConfigArgs()}'")
      preambleEmitter.emitPreamble(smt2ConfigOptions)
    }

    decider.prover.logComment("\n; /preamble.smt2")
    preambleEmitter.emitPreamble("/preamble.smt2")

    decider.pushScope()
  }
}
