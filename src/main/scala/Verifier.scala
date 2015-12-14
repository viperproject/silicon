/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon

import org.slf4s.Logging
import viper.silver.ast
import viper.silver.components.StatefulComponent
import viper.silicon.interfaces._
import viper.silicon.interfaces.decider.Decider
import viper.silicon.interfaces.state._
import viper.silicon.interfaces.state.factoryUtils.Ø
import viper.silicon.decider.PreambleFileEmitter
import viper.silicon.state.{IdentifierFactory, terms, SymbolConvert, DefaultContext}
import viper.silicon.state.terms.{sorts, Sort}
import viper.silicon.supporters._
import viper.silicon.supporters.functions.FunctionSupporterProvider
import viper.silicon.supporters.qps.{FieldValueFunctionsEmitter, QuantifiedChunkSupporter}
import viper.silicon.reporting.Bookkeeper

/* TODO: 1. Extract method verification code into a MethodSupporter
 *       2. Remove this trait
 */
trait AbstractElementVerifier[ST <: Store[ST],
                             H <: Heap[H], PC <: PathConditions[PC],
                             S <: State[ST, H, S]]
    extends Logging
       with Evaluator[ST, H, S, DefaultContext[H]]
       with Producer[ST, H, S, DefaultContext[H]]
       with Consumer[Chunk, ST, H, S, DefaultContext[H]]
       with Executor[ST, H, S, DefaultContext[H]]
   { this: MagicWandSupporter[ST, H, PC, S] =>

  private type C = DefaultContext[H]

  /*protected*/ val config: Config

  /*protected*/ val decider: Decider[ST, H, PC, S, C]
  import decider.{fresh, inScope}

  /*protected*/ val stateFactory: StateFactory[ST, H, S]
  import stateFactory._

  /*protected*/ val stateFormatter: StateFormatter[ST, H, S, String]
  /*protected*/ val symbolConverter: SymbolConvert

  val quantifiedChunkSupporter: QuantifiedChunkSupporter[ST, H, PC, S]

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
                consumes(σ2, terms.FullPerm(), posts, postViolated, c3)((σ3, _, _, c4) =>
                  Success()))})})}
  }
}

/* A base implementation of start/reset/stop is required by the
 * DefaultElementVerifier, Scala will (rightfully) complain otherwise.
 */
class NoOpStatefulComponent extends StatefulComponent {
  @inline def start() {}
  @inline def reset() {}
  @inline def stop() {}
}

class DefaultElementVerifier[ST <: Store[ST],
                             H <: Heap[H],
                             PC <: PathConditions[PC],
                             S <: State[ST, H, S]]
    (val config: Config,
     val decider: Decider[ST, H, PC, S, DefaultContext[H]],
     val stateFactory: StateFactory[ST, H, S],
     val symbolConverter: SymbolConvert,
     val stateFormatter: StateFormatter[ST, H, S, String],
     val heapCompressor: HeapCompressor[ST, H, S, DefaultContext[H]],
     val quantifiedChunkSupporter: QuantifiedChunkSupporter[ST, H, PC, S],
     val bookkeeper: Bookkeeper,
     val identifierFactory: IdentifierFactory)
    (protected implicit val manifestH: Manifest[H])
    extends NoOpStatefulComponent
       with AbstractElementVerifier[ST, H, PC, S]
       with DefaultEvaluator[ST, H, PC, S]
       with DefaultProducer[ST, H, PC, S]
       with DefaultConsumer[ST, H, PC, S]
       with DefaultExecutor[ST, H, PC, S]
       with FunctionSupporterProvider[ST, H, PC, S]
       with ChunkSupporter[ST, H, PC, S]
       with PredicateSupporterProvider[ST, H, PC, S]
       with DefaultBrancher[ST, H, PC, S]
       with DefaultJoiner[ST, H, PC, S]
       with DefaultLetHandler[ST, H, S, DefaultContext[H]]
       with MagicWandSupporter[ST, H, PC, S]
       with HeuristicsSupporter[ST, H, PC, S]
       with Logging

trait AbstractVerifier[ST <: Store[ST],
                       H <: Heap[H],
                       PC <: PathConditions[PC],
                       S <: State[ST, H, S]]
    extends Logging {

  /*protected*/ def decider: Decider[ST, H, PC, S, DefaultContext[H]]
  /*protected*/ def config: Config
  /*protected*/ def bookkeeper: Bookkeeper
  /*protected*/ def preambleEmitter: PreambleFileEmitter[String, String]
  /*protected*/ def sequencesEmitter: SequencesEmitter
  /*protected*/ def setsEmitter: SetsEmitter
  /*protected*/ def multisetsEmitter: MultisetsEmitter
  /*protected*/ def domainsEmitter: DomainsEmitter
  /*protected*/ def fieldValueFunctionsEmitter: FieldValueFunctionsEmitter

  val ev: DefaultElementVerifier[ST, H, PC, S]

  /* Functionality */

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
      ev.quantifiedChunkSupporter.initLastFVF(c.qpFields) /* TODO: Implement properly */

      ev.verify(method, c)
    })

    (   functionVerificationResults
     ++ predicateVerificationResults
     ++ methodVerificationResults)
  }

  private def filter(str: String) = (
       !str.matches(config.includeMembers())
    || str.matches(config.excludeMembers()))

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

class DefaultVerifier[ST <: Store[ST],
                      H <: Heap[H] : Manifest,
                      PC <: PathConditions[PC],
                      S <: State[ST, H, S]]
    (val config: Config,
     val decider: Decider[ST, H, PC, S, DefaultContext[H]],
     val stateFactory: StateFactory[ST, H, S],
     val symbolConverter: SymbolConvert,
     val preambleEmitter: PreambleFileEmitter[String, String],
     val sequencesEmitter: SequencesEmitter,
     val setsEmitter: SetsEmitter,
     val multisetsEmitter: MultisetsEmitter,
     val domainsEmitter: DomainsEmitter,
     val fieldValueFunctionsEmitter: FieldValueFunctionsEmitter,
     val stateFormatter: StateFormatter[ST, H, S, String],
     val heapCompressor: HeapCompressor[ST, H, S, DefaultContext[H]],
     val quantifiedChunkSupporter: QuantifiedChunkSupporter[ST, H, PC, S],
     val bookkeeper: Bookkeeper,
     val identifierFactory: IdentifierFactory)
    extends AbstractVerifier[ST, H, PC, S]
       with StatefulComponent
       with Logging {

  val ev = new DefaultElementVerifier(config, decider, stateFactory, symbolConverter, stateFormatter, heapCompressor,
                                      quantifiedChunkSupporter, bookkeeper, identifierFactory)

  private val statefulSubcomponents = List[StatefulComponent](
    bookkeeper,
    preambleEmitter, sequencesEmitter, setsEmitter, multisetsEmitter, domainsEmitter,
    fieldValueFunctionsEmitter, quantifiedChunkSupporter,
    decider, identifierFactory.asInstanceOf[StatefulComponent],
    ev, ev.functionsSupporter, ev.predicateSupporter)

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
}
