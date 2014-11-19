/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon

import com.weiglewilczek.slf4s.Logging
import silver.ast.Position
import util.control.Breaks._
import silver.verifier.errors.{ContractNotWellformed, PostconditionViolated, Internal, FunctionNotWellformed,
    PredicateNotWellformed, MagicWandNotWellformed}
import silver.components.StatefulComponent
import silver.ast.utility.{Nodes, Visitor}
import interfaces.{Evaluator, Producer, Consumer, Executor, VerificationResult, Success, Failure}
import interfaces.decider.Decider
import interfaces.state.{Store, Heap, PathConditions, State, StateFactory, StateFormatter, HeapCompressor, Chunk}
import interfaces.state.factoryUtils.Ø
import state.{DefaultContext, terms, SymbolConvert}
import state.terms.{sorts, Sort}
import theories.{FunctionsSupporter, DomainsEmitter, SetsEmitter, MultisetsEmitter, SequencesEmitter}
import reporting.Bookkeeper
import decider.PreambleFileEmitter
import supporters.MagicWandSupporter

trait AbstractElementVerifier[ST <: Store[ST],
														 H <: Heap[H], PC <: PathConditions[PC],
														 S <: State[ST, H, S]]
		extends Logging
		   with Evaluator[ST, H, S, DefaultContext[H]]
		   with Producer[ST, H, S, DefaultContext[H]]
		   with Consumer[Chunk, ST, H, S, DefaultContext[H]]
		   with Executor[ST, H, S, DefaultContext[H]]
       with FunctionsSupporter[ST, H, PC, S] {

  private type C = DefaultContext[H]

  /*protected*/ val config: Config

  /*protected*/ val decider: Decider[ST, H, PC, S, C]
  import decider.{fresh, inScope}

  /*protected*/ val stateFactory: StateFactory[ST, H, S]
  import stateFactory._

  /*protected*/ val stateFormatter: StateFormatter[ST, H, S, String]
  /*protected*/ val symbolConverter: SymbolConvert

  def verify(program: ast.Program, member: ast.Member, c: C): VerificationResult = {
    member match {
      case m: ast.Method => verify(m, c)
      case f: ast.ProgramFunction => sys.error("Functions unexpected at this point, should have been handled already")
      case p: ast.Predicate => verify(p, c)
      case _: ast.Domain | _: ast.Field => Success()
    }
  }

  private def checkWandsAreSelfFraming(γ: ST, g: H, root: ast.Member, c: C): VerificationResult = {
    val wands = Visitor.deepCollect(List(root), Nodes.subnodes){case wand: ast.MagicWand => wand}
    var result: VerificationResult = Success()

//    println("\n[checkWandsAreSelfFraming]")

    breakable {
      wands foreach {_wand =>
        val err = MagicWandNotWellformed(_wand)

        /* TODO: How to handle magic wand chunk terms (e.g., wand w := ...) when
         * checking self-framingness of wands? This also raises the question of
         * how to produce such terms in general, which could happen when
         * checking self-framingness of wands, but also, if such terms appear
         * on the left of a wand that is packaged.
         *
         * The problem is currently avoided by replacing occurences of wand
         * chunk terms with the trivial wand true --* true. Not sure if this is
         * sound, though.
         */
        val trivialWand = (p: Position) => ast.MagicWand(ast.True()(p), ast.True()(p))(p)
        val wand = _wand.transform {
          case v: ast.Variable if v.typ == ast.types.Wand => trivialWand(v.pos)
        }()

        val left = wand.left
        val right = wand.withoutGhostOperations.right
        val vs = Visitor.deepCollect(List(left, right), Nodes.subnodes){case v: ast.Variable => v}
        val γ1 = Γ(vs.map(v => (v, fresh(v))).toIterable) + γ
        val σ1 = Σ(γ1, Ø, g)

//        println(s"  left = $left")
//        println(s"  right = $right")
//        println(s"  s1.γ = ${σ1.γ}")
//        println(s"  s1.h = ${σ1.h}")
//        println(s"  s1.g = ${σ1.g}")

        var σInner: S = null

        result =
          inScope {
//            println("  checking left")
            produce(σ1, fresh, terms.FullPerm(), left, err, c)((σ2, c2) => {
              σInner = σ2
//              val c3 = c2 /*.copy(givenHeap = Some(σ2.h))*/
//              val σ3 = σ1
              Success()})
          } && inScope {
//            println("  checking right")
            produce(σ1, fresh, terms.FullPerm(), right, err, c.copy(lhsHeap = Some(σInner.h)))((_, c4) =>
              Success())}

//        println(s"  result = $result")

        result match {
          case failure: Failure[ST@unchecked, H@unchecked, S@unchecked] =>
            /* Failure occurred. We transform the original failure into a MagicWandNotWellformed one. */
            result = failure.copy[ST, H, S](message = MagicWandNotWellformed(wand, failure.message.reason))
            break()

          case _: Success => /* Nothing needs to be done*/
        }
      }
    }

    result
  }

  def verify(method: ast.Method, c: C): VerificationResult = {
    logger.debug("\n\n" + "-" * 10 + " METHOD " + method.name + "-" * 10 + "\n")
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

    val postViolated = (offendingNode: ast.Expression) => PostconditionViolated(offendingNode, method)

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
              checkWandsAreSelfFraming(σ1.γ, σ1.h, method, c2)}
        && inScope {
              produces(σ2, fresh, terms.FullPerm(), posts, ContractNotWellformed, c2)((_, c3) =>
                Success())}
        && inScope {
              exec(σ1 \ (g = σ1.h), body, c2)((σ2, c3) =>
                consumes(σ2, terms.FullPerm(), posts, postViolated, c3)((σ3, _, _, c4) =>
                  Success()))})})}
  }

  def verify(predicate: ast.Predicate, c: C): VerificationResult = {
    logger.debug("\n\n" + "-" * 10 + " PREDICATE " + predicate.name + "-" * 10 + "\n")
    decider.prover.logComment("%s %s %s".format("-" * 10, predicate.name, "-" * 10))

    val ins = predicate.formalArgs.map(_.localVar)

    val γ = Γ(ins.map(v => (v, fresh(v))))
    val σ = Σ(γ, Ø, Ø)

       (inScope {
          checkWandsAreSelfFraming(σ.γ, σ.h, predicate, c)}
    && inScope {
          produce(σ, fresh, terms.FullPerm(), predicate.body, PredicateNotWellformed(predicate), c)((_, c1) =>
            Success())})
  }
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
     val stateUtils: StateUtils[ST, H, PC, S, DefaultContext[H]],
     val bookkeeper: Bookkeeper)
    (protected implicit val manifestH: Manifest[H])
		extends AbstractElementVerifier[ST, H, PC, S]
       with DefaultEvaluator[ST, H, PC, S]
       with DefaultProducer[ST, H, PC, S]
       with DefaultConsumer[ST, H, PC, S]
       with DefaultExecutor[ST, H, PC, S]
       with DefaultBrancher[ST, H, PC, S, DefaultContext[H]]
       with DefaultJoiner[ST, H, PC, S]
       with DefaultLetHandler[ST, H, S, DefaultContext[H]]
       with MagicWandSupporter[ST, H, PC, S]
       with Logging

trait AbstractVerifier[ST <: Store[ST],
                       H <: Heap[H],
                       PC <: PathConditions[PC],
                       S <: State[ST, H, S]]
    extends StatefulComponent
       with Logging {

  /*protected*/ def decider: Decider[ST, H, PC, S, DefaultContext[H]]
  /*protected*/ def config: Config
  /*protected*/ def bookkeeper: Bookkeeper
  /*protected*/ def preambleEmitter: PreambleFileEmitter[String, String]
  /*protected*/ def sequencesEmitter: SequencesEmitter
  /*protected*/ def setsEmitter: SetsEmitter
  /*protected*/ def multisetsEmitter: MultisetsEmitter
  /*protected*/ def domainsEmitter: DomainsEmitter

  val ev: AbstractElementVerifier[ST, H, PC, S]

  private val statefulSubcomponents = List[StatefulComponent](
    bookkeeper,
    preambleEmitter, sequencesEmitter, setsEmitter, multisetsEmitter, domainsEmitter,
    decider)

  /* Lifetime */

  def start() {
    statefulSubcomponents foreach (_.start())
  }

  def reset() {
    utils.counter.reset()
    statefulSubcomponents foreach (_.reset())
  }

  def stop() {
    statefulSubcomponents foreach (_.stop())
  }

  /* Functionality */

  def verify(program: ast.Program): List[VerificationResult] = {
    emitPreamble(program)

    ev.functionsSupporter.handleFunctions(program) ++ verifyMembersOtherThanFunctions(program)
  }

  private def verifyMembersOtherThanFunctions(program: ast.Program): List[VerificationResult] = {
    val c = DefaultContext[H](program)

    val members = program.members.filterNot {
      case func: ast.ProgramFunction => true
      case m => filter(m.name)
    }

    /* TODO: Verification could be parallelised by forking DefaultMemberVerifiers. */

    /* Verify members. Verification continues if errors are found, i.e.
     * all members are verified regardless of previous errors.
     * However, verification of a single member is aborted on first error.
     */
    members.map(m => ev.verify(program, m, c)).toList
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

    emitStaticPreamble()

    sequencesEmitter.declareSorts()
    setsEmitter.declareSorts()
    multisetsEmitter.declareSorts()
    domainsEmitter.declareSorts()

    /* Sequences depend on multisets ($Multiset.fromSeq, which is
     * additionally axiomatised in the sequences axioms).
     * Multisets depend on sets ($Multiset.fromSet).
     */
    setsEmitter.declareSymbols()
    multisetsEmitter.declareSymbols()
    sequencesEmitter.declareSymbols()
    domainsEmitter.declareSymbols()
    domainsEmitter.emitUniquenessAssumptions()

    sequencesEmitter.emitAxioms()
    setsEmitter.emitAxioms()
    multisetsEmitter.emitAxioms()
    domainsEmitter.emitAxioms()

    emitSortWrappers(Set(sorts.Int, sorts.Bool, sorts.Ref, sorts.Perm))
    emitSortWrappers(sequencesEmitter.sorts)
    emitSortWrappers(setsEmitter.sorts)
    emitSortWrappers(multisetsEmitter.sorts)
    emitSortWrappers(domainsEmitter.sorts)

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
     val stateFormatter: StateFormatter[ST, H, S, String],
     val heapCompressor: HeapCompressor[ST, H, S, DefaultContext[H]],
     val stateUtils: StateUtils[ST, H, PC, S, DefaultContext[H]],
     val bookkeeper: Bookkeeper)
		extends AbstractVerifier[ST, H, PC, S]
       with Logging {

  val ev = new DefaultElementVerifier(config, decider, stateFactory, symbolConverter, stateFormatter, heapCompressor,
                                      stateUtils, bookkeeper)

  override def reset() {
    super.reset()
    ev.fappCache = Map()
    ev.fappCacheFrames = Stack()
    ev.currentGuards = Set()
  }
}
