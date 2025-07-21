// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.rules

import scala.annotation.unused
import org.slf4j.LoggerFactory
import viper.silicon.Stack
import viper.silver.ast
import viper.silver.verifier.PartialVerificationError
import viper.silver.verifier.errors.HeuristicsFailed
import viper.silver.verifier.reasons.InsufficientPermission
import viper.silicon.interfaces._
import viper.silicon.interfaces.state._
import viper.silicon.resources.{FieldID, PredicateID}
import viper.silicon.state._
import viper.silicon.state.terms.{True, _}
import viper.silicon.verifier.Verifier
import viper.silver.ast.{Exp, PredicateAccess}

object foldHeuristicsSupporter extends SymbolicExecutionRules {

  import executor._

  /* tryOperation-Methods with varying output arity */

  @inline
  def tryOperation[O1]
  (description: String)
  (s: State, h: Heap, v: Verifier)
  (action: (State, Heap, Verifier, (State, O1, Verifier) => VerificationResult) => VerificationResult)
  (Q: (State, O1, Verifier) => VerificationResult)
  : VerificationResult = {

    tryWithReactions[O1](description)(s, h, v)(action, None)(Q)
  }

  @inline
  def tryOperation[O1, O2]
  (description: String)
  (s: State, h: Heap, v: Verifier)
  (action: (State, Heap, Verifier, (State, O1, O2, Verifier) => VerificationResult) => VerificationResult)
  (Q: (State, O1, O2, Verifier) => VerificationResult)
  : VerificationResult = {

    val tupledAction = (s1: State, h1: Heap, v1: Verifier, QS: (State, (O1, O2), Verifier) => VerificationResult) =>
      action(s1, h1, v1, (s2, o1: O1, o2: O2, v2) => QS(s2, (o1, o2), v2))

    val tupledQ = (s1: State, os: (O1, O2), v1: Verifier) => Q(s1, os._1, os._2, v1)

    tryWithReactions[(O1, O2)](description)(s, h, v)(tupledAction, None)(tupledQ)
  }

  /* tryWithReactions, which executes the action-reaction cycle */

  private var cnt = 0L
  private var stack = Stack[Long]()
  private val heuristicsLogger = LoggerFactory.getLogger("heuristics")

  private def tryWithReactions[O]
  (description: String)
  (_s: State, h: Heap, v: Verifier)
  (action: (State, Heap, Verifier, (State, O, Verifier) => VerificationResult) => VerificationResult,
   initialFailure: Option[Failure])
  (Q: (State, O, Verifier) => VerificationResult)
  : VerificationResult = {
    if (!Verifier.config.enableAutomaticFolding()) {
      return action(_s, h, v, Q)
    }

    val myId = cnt;
    cnt += 1
    val baseIdent = "  "
    var printedHeader = false

    def lnsay(msg: String, ident: Int = 1): Unit = {
      val prefix = "\n" + (if (ident == 0) "" else baseIdent)
      dosay(prefix, msg, ident - 1)
    }

    def say(msg: String, ident: Int = 1): Unit = {
      val prefix = if (ident == 0) "" else baseIdent
      dosay(prefix, msg, ident - 1)
    }

    def dosay(prefix: String, msg: String, ident: Int): Unit = {
      if (!printedHeader) {
        heuristicsLogger.error("\n[tryWithReactions]")
        printedHeader = true
      }

      val messagePrefix = baseIdent * ident
      heuristicsLogger.error(s"$prefix($myId)$messagePrefix $msg")
    }


    var localActionSuccess = false
    val s = _s

    val globalActionResult =
      action(s, h, v, (s1, outputs, v1) => {
        /* We are here if the `action` invoked the success continuation `QS` */
        localActionSuccess = true
        Q(s1, outputs, v1)
      })

    /* The `action` is either a regular piece of symbolic execution code, e.g.,
     * a part of a rule in the consumer, that is wrapped by `tryOperation`, or
     * it is a reaction that was chosen by a heuristic.
     *
     * The former is expected to invoke the success continuation `QS` that is
     * passed to the action by `tryOperation` in order to indicate that the
     * action locally succeeds. The goal of this is to not apply heuristics
     * if an action failed after it locally succeeded, which in turn reduces
     * the number of reactions, and thereby, symbolic execution branches.
     *
     * The latter is *not* expected to invoke the success continuation `QS`,
     * because we want to backtrack over unsuccessful reactions in order to
     * try the next reaction on the same depth. Moreover, the depth will be
     * reset to 0 in the `QS`, which allows further (nested) heuristics.
     */

    var reactionResult: VerificationResult = globalActionResult
    /* A bit hacky, but having an initial result here simplifies things quite a bit */

    if (!localActionSuccess) {
      (globalActionResult: @unchecked) match {
        case _ if localActionSuccess
          || !globalActionResult.isFatal
          //|| !s.applyHeuristics
          || s.heuristicsDepth > Verifier.config.maxHeuristicsDepth() =>
          /* Quit trying heuristics */

        case actionFailure: Failure =>
          stack ::= myId

          var remainingReactions = generateReactions(s, h, v, actionFailure)
          var triedReactions = 0

          while (reactionResult.isFatal && remainingReactions.nonEmpty) {
            lnsay(s"trying next reaction (${triedReactions + 1} out of ${triedReactions + remainingReactions.length}) for $description")

            val s1 = s.copy(h = h, heuristicsDepth = s.heuristicsDepth + 1)
            //          bookkeeper.appliedHeuristicReactions += 1

            reactionResult =
              foldHeuristicsSupporter.tryOperation[Heap](s"applying heuristic")(s1, h, v)((s2, h2, v2, QS) =>
                remainingReactions.head.apply(s2, h2, v2)((s3, h3, v3) => {
                  say(s"reaction ${triedReactions + 1} locally succeeded")
                  say(s"s3.h = ${v3.stateFormatter.format(s3.h)}")
                  say(s"h3 = ${v2.stateFormatter.format(h3)}")
                  say(s"c3.reserveHeaps:")
                  s3.reserveHeaps.map(v3.stateFormatter.format).foreach(str => say(str, 2))
                  QS(s3, h3, v3)
                })
              )((s4, h4, c4) => {
                tryWithReactions(description)(s4, h4, c4)(action, initialFailure.orElse(Some(actionFailure)))(Q)
              })

            lnsay(s"returned from reaction ${triedReactions + 1} (out of ${triedReactions + remainingReactions.length})")
            say(s"reactionResult = $reactionResult")

            triedReactions += 1

            remainingReactions = remainingReactions.tail
          }

          if (stack.nonEmpty) {
            // TODO: Emptiness check should not be necessary, but currently is. Find out, why.
            stack = stack.tail
          }

          lnsay(s"existing tryWithReactions")
          say(s"localActionSuccess = $localActionSuccess")
          say(s"reactionResult = $reactionResult")
      }
    }

    (reactionResult: @unchecked) match {
      case _ if !reactionResult.isFatal =>
        reactionResult

      case _: Failure =>
        if (localActionSuccess) globalActionResult else initialFailure.getOrElse(globalActionResult)
    }
  }

  def generateReactions(s: State, h: Heap, @unused v: Verifier, cause: Failure)
  : Seq[(State, Heap, Verifier) => ((State, Heap, Verifier) => VerificationResult) => VerificationResult] = {

    val pve = HeuristicsFailed(ast.TrueLit()()) /* TODO: Use a meaningful node */

    def ok(e: ast.Exp) = !e.existsDefined { case lv: ast.AbstractLocalVar if s.g.get(lv).isEmpty => }

    cause.message.reason match {
      case reason: InsufficientPermission =>
        val locationMatcher = matchers.location(reason.offendingNode.loc(s.program), s.program)
        val predicateAccesses = predicateInstancesMatching(s, h, v, locationMatcher)
        val unfoldPredicateReactions = predicateAccesses flatMap {
          case acc if ok(acc) => Some(unfoldPredicate(acc, pve) _)
          case _ => None
        }

        val foldPredicateReaction =
          reason.offendingNode match {
            case pa: ast.PredicateAccess if ok(pa) =>
              Some(
                getFolds(
                  ast.PredicateAccessPredicate(pa, Some(ast.FullPerm()()))(),
                  s.program,
                  pve)
                  _
              )
            case _ => None
          }

        unfoldPredicateReactions ++ foldPredicateReaction

      case _ => Nil
    }
  }

  /* Heuristics */

  def unfoldPredicate(acc: ast.PredicateAccessPredicate, @unused pve: PartialVerificationError)
                     (s: State, h: Heap, v: Verifier)
                     (Q: (State, Heap, Verifier) => VerificationResult)
  : VerificationResult = {

    val unfoldStmt = ast.Unfold(acc)()
    exec(s.copy(h = h), unfoldStmt, v)((s1, v1) =>
      Q(s1, s1.h, v1))
  }

  private def getFolds(exp: Exp, program: ast.Program, pve: PartialVerificationError)
              (s: State, h: Heap, v: Verifier)
              (Q: (State, Heap, Verifier) => VerificationResult)
  : VerificationResult = {
    if (s.heuristicsDepth <= Verifier.config.maxHeuristicsDepth()) {
      exp match {
        case ast.Implies(left, right) =>
          return evaluator.eval(s, left, pve, v)(
            (s1, t1, e1, v1) => brancher.branch(s1, t1, (left, e1), v1)(
              (s2, v2) => {
                collectStmts(right.topLevelConjuncts, program, pve)(s2, s2.h, v2)((s3, h3, v3) => Q(s3, h3, v3))
              },
              (s4, v4) => {
                Q(s4, s4.h, v4)
              })
          )
        case pa: ast.PredicateAccessPredicate =>
          return evaluator.evals(s, pa.loc.args, _ => pve, v)((s_args, tArgs, _, v_args) => {
            val alreadyInHeap = (s_args.h.values ++ h.values).exists {
              case ch: BasicChunk if ch.resourceID == PredicateID &&
                                     ch.id.name == pa.loc.predicateName &&
                                     ch.args == tArgs => true
              case _ => false
            }
            if (alreadyInHeap) {
              Q(s_args, s_args.h, v_args)
            } else {
              val foldStmt = ast.Fold(ast.PredicateAccessPredicate(pa.loc, Some(ast.FullPerm()()))())()
              collectStmts(
                pa.loc.predicateBody(program, pa.loc.args.map(a => a.toString).toSet).get.topLevelConjuncts,
                program,
                pve)(s_args.copy(heuristicsDepth = s_args.heuristicsDepth + 1), s_args.h, v_args)(
                (s1, _, v1) => {
                  exec(s1, foldStmt, v1)((s2, v2) => Q(s2, s2.h, v2))
                })
            }
          })
        case _ => {
          return exec(s, ast.Inhale(ast.TrueLit()())(), v)((s1, v1) => Q(s1, s1.h, v1))
        }
      }
    }

    Q(s, h, v)
  }

  private def collectStmts(exps: Seq[Exp], program: ast.Program, pve: PartialVerificationError)
                  (s: State, h: Heap, v: Verifier)
                  (Q: (State, Heap, Verifier) => VerificationResult)
  : VerificationResult = {
    if (s.heuristicsDepth <= Verifier.config.maxHeuristicsDepth() && exps.nonEmpty) {
      return getFolds(exps.head, program, pve)(s, h, v)((s1, h1, v1) => collectStmts(exps.tail, program, pve)(s1, h1, v1)(Q)
      )
    }

    Q(s, h, v)
  }

  /* Helpers */
  private def predicateInstancesMatching(s: State, h: Heap, @unused v: Verifier, f: PartialFunction[ast.Node, _]): Seq[ast.PredicateAccessPredicate] = {
    val allChunks = (s.h.values ++ h.values ++ s.reserveHeaps.flatMap(_.values)).toSeq.distinct
    val program = s.program

    val predicateChunks =
      allChunks.collect {
        case ch: BasicChunk if ch.resourceID == PredicateID =>
          val body = program.findPredicate(ch.id.name)

          if (body.existsDefined(f)) {
            Some(ch)
          } else {
            None
          }
      }.flatten

    val predicateAccesses =
      predicateChunks.flatMap {
        case BasicChunk(PredicateID, BasicChunkIdentifier(name), args, _, _, _, _, _) =>
          val reversedArgs: Seq[ast.Exp] = backtranslate(s.g.values, allChunks, args, program)

          if (args.length == reversedArgs.length)
            Some(ast.PredicateAccessPredicate(ast.PredicateAccess(reversedArgs, name)(), Some(ast.FullPerm()()))())
          else
            None
        case _ => sys.error("Unexpected case in pattern matching")
      }

    predicateAccesses
  }

  object matchers {
    def location(loc: ast.Location, program: ast.Program): PartialFunction[ast.Node, Any] = {
      case ast.AccessPredicate(locacc: ast.LocationAccess, _) if locacc.loc(program) == loc =>
    }

    def structure(wand: ast.MagicWand, program: ast.Program): PartialFunction[ast.Node, Any] = {
      case other: ast.MagicWand if MagicWandIdentifier(wand, program) == MagicWandIdentifier(other, program) =>
    }
  }

  private def backtranslate(bindings: Map[ast.AbstractLocalVar, (Term, Option[Exp])], chunks: Seq[Chunk], ts: Seq[Term], program: ast.Program)
  : Seq[ast.Exp] = {

    val optEs =
      ts map {
        case True => Some(ast.TrueLit()())
        case False => Some(ast.FalseLit()())
        case IntLiteral(n) => Some(ast.IntLit(n)())
        case t =>
          bindings.find(p => p._2._1 == t)
            .map(_._1)
            .orElse(iterateChunks(bindings, chunks, t, program).map(v => ast.FieldAccess(v._2, program.findField(v._1))()))
      }

    optEs.flatten
  }

  private def iterateChunks(bindings: Map[ast.AbstractLocalVar, (Term, Option[Exp])], chunks: Seq[Chunk], t: Term, program: ast.Program): Option[(String, ast.Exp)] = {
    chunks.foreach {
      case fc: BasicChunk if fc.resourceID == FieldID && fc.snap == t =>
        return bindings.find(p => p._2._1 == fc.args.head)
          .map(a => (fc.id.name, a._1))
          .orElse(
            iterateChunks(bindings, chunks.filterNot(_ == fc), fc.args.head, program)
              .flatMap(v => Some((fc.id.name, ast.FieldAccess(v._2, program.findField(v._1))())))
          )
      case _ =>
    }
    None
  }
}