// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.rules

import java.util.concurrent.atomic.AtomicLong
import org.slf4j.LoggerFactory
import viper.silver.ast
import viper.silver.verifier.PartialVerificationError
import viper.silver.verifier.errors.HeuristicsFailed
import viper.silver.verifier.reasons.InsufficientPermission
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.interfaces._
import viper.silicon.resources.PredicateID
import viper.silicon.state._
import viper.silicon.state.terms._
import viper.silicon.verifier.Verifier

/** A resource instance that a failing operation required: the resource, its arguments and,
  * if the operation consumes the resource, the amount of permission to consume.
  */
case class MissingResource(resource: ast.Resource,
                           args: Seq[Term],
                           argsExp: Option[Seq[ast.Exp]],
                           perm: Option[(Term, Option[ast.Exp])])

object foldHeuristicsSupporter extends SymbolicExecutionRules {

  private type Reaction = (State, Heap, Verifier) => ((State, Heap, Verifier) => VerificationResult) => VerificationResult

  /* tryOperation-Methods with varying output arity */

  @inline
  def tryOperation[O1]
  (description: String, missing: Option[MissingResource])
  (s: State, h: Heap, v: Verifier)
  (action: (State, Heap, Verifier, (State, O1, Verifier) => VerificationResult) => VerificationResult)
  (Q: (State, O1, Verifier) => VerificationResult)
  : VerificationResult = {

    tryWithReactions[O1](description, missing)(s, h, v)(action, None)(Q)
  }

  @inline
  def tryOperation[O1, O2]
  (description: String, missing: Option[MissingResource])
  (s: State, h: Heap, v: Verifier)
  (action: (State, Heap, Verifier, (State, O1, O2, Verifier) => VerificationResult) => VerificationResult)
  (Q: (State, O1, O2, Verifier) => VerificationResult)
  : VerificationResult = {

    val tupledAction = (s1: State, h1: Heap, v1: Verifier, QS: (State, (O1, O2), Verifier) => VerificationResult) =>
      action(s1, h1, v1, (s2, o1: O1, o2: O2, v2) => QS(s2, (o1, o2), v2))

    val tupledQ = (s1: State, os: (O1, O2), v1: Verifier) => Q(s1, os._1, os._2, v1)

    tryWithReactions[(O1, O2)](description, missing)(s, h, v)(tupledAction, None)(tupledQ)
  }

  /* tryWithReactions, which executes the action-reaction cycle */

  private val reactionCounter = new AtomicLong()
  private val heuristicsLogger = LoggerFactory.getLogger("heuristics")

  private def tryWithReactions[O]
  (description: String, missing: Option[MissingResource])
  (s: State, h: Heap, v: Verifier)
  (action: (State, Heap, Verifier, (State, O, Verifier) => VerificationResult) => VerificationResult,
   initialFailure: Option[Failure],
   baseDepth: Int = -1)
  (Q: (State, O, Verifier) => VerificationResult)
  : VerificationResult = {
    if (!Verifier.config.enableAutomaticFolding()) {
      return action(s, h, v, Q)
    }

    val myId = reactionCounter.getAndIncrement()
    /* The heuristics depth at which the original (non-reaction) action was attempted */
    val depth = if (baseDepth < 0) s.heuristicsDepth else baseDepth

    def say(msg: => String): Unit =
      if (heuristicsLogger.isDebugEnabled) heuristicsLogger.debug(s"($myId) $msg")

    var localActionSuccess = false

    val globalActionResult =
      action(s, h, v, (s1, outputs, v1) => {
        /* We are here if the `action` invoked the success continuation `QS` */
        localActionSuccess = true
        Q(s1.copy(heuristicsDepth = depth), outputs, v1)
      })

    /* The `action` is a regular piece of symbolic execution code, e.g., a part
     * of a rule in the consumer, that is wrapped by `tryOperation`. It is
     * expected to invoke the success continuation `QS` that is passed to it in
     * order to indicate that the action locally succeeds. If the action failed
     * after it locally succeeded, then the failure stems from a later part of
     * the symbolic execution, and it is reported as is: no heuristics are
     * applied, which in turn reduces the number of reactions, and thereby,
     * symbolic execution branches.
     *
     * Otherwise, reactions chosen by the heuristics are tried one after the
     * other, each followed by a retry of the action, until the action locally
     * succeeds after one of them.
     */

    if (localActionSuccess || !globalActionResult.isFatal || s.heuristicsDepth > Verifier.config.maxHeuristicsDepth()) {
      return globalActionResult
    }

    globalActionResult match {
      case actionFailure: Failure =>
        /* The failure of the original action is the one reported if no reaction helps */
        val originalFailure = initialFailure.getOrElse(actionFailure)
        val reactions = generateReactions(s, h, actionFailure, missing)

        var reactionResult: VerificationResult = originalFailure
        var reactionSuccess = false
        var triedReactions = 0

        while (reactionResult.isFatal && !reactionSuccess && triedReactions < reactions.length) {
          say(s"trying reaction ${triedReactions + 1} out of ${reactions.length} for $description")

          val s1 = s.copy(h = h, heuristicsDepth = s.heuristicsDepth + 1)

          /* Assumptions made by an unsuccessful reaction must not leak into the next one */
          v.decider.pushScope()
          val result =
            reactions(triedReactions)(s1, h, v)((s2, h2, v2) => {
              say(s"reaction ${triedReactions + 1} locally succeeded, h2 = ${v2.stateFormatter.format(h2)}")
              tryWithReactions(description, missing)(s2, h2, v2)(action, Some(originalFailure), depth)((s3, outputs, v3) => {
                reactionSuccess = true
                Q(s3, outputs, v3)
              })
            })
          v.decider.popScope()

          say(s"reaction ${triedReactions + 1} returned $result (action locally succeeded: $reactionSuccess)")

          triedReactions += 1

          /* If the action locally succeeded after the reaction, then any failure stems
           * from later parts of the symbolic execution and is reported as is.
           */
          if (reactionSuccess || !result.isFatal) reactionResult = result
        }

        reactionResult

      case _ => globalActionResult
    }
  }

  /** Reactions for the given failure: unfolding predicate instances whose body provides the
    * missing resource, and folding the missing resource if it is a predicate instance.
    */
  private def generateReactions(s: State, h: Heap, cause: Failure, missing: Option[MissingResource])
  : Seq[Reaction] = {

    (cause.message.reason, missing) match {
      case (_: InsufficientPermission, Some(missing)) =>
        val unfoldReactions: Seq[Reaction] =
          predicateChunksProviding(s, h, missing).map(ch => unfoldPredicate(ch) _)

        val foldReaction: Option[Reaction] =
          (missing.resource, missing.perm) match {
            case (predicate: ast.Predicate, Some((tPerm, ePerm))) if predicate.body.nonEmpty =>
              val pa = ast.PredicateAccess(missing.argsExp.getOrElse(predicate.formalArgs.map(_.localVar)), predicate.name)()
              Some(foldPredicate(predicate, pa, missing.args, missing.argsExp, tPerm, ePerm) _)
            case _ => None
          }

        unfoldReactions ++ foldReaction

      case _ => Nil
    }
  }

  /* Heuristics */

  /** Unfolds the given predicate chunk, using exactly the permission amount held by the chunk.
    * Unfolding is done on the level of terms, so that no expressions for the predicate's
    * arguments need to be reconstructed.
    */
  private def unfoldPredicate(ch: BasicChunk)
                             (s: State, h: Heap, v: Verifier)
                             (Q: (State, Heap, Verifier) => VerificationResult)
  : VerificationResult = {

    val predicate = s.program.findPredicate(ch.id.name)
    val pa = ast.PredicateAccess(ch.argsExp.getOrElse(predicate.formalArgs.map(_.localVar)), predicate.name)()
    val pve = HeuristicsFailed(pa)

    predicateSupporter.unfold(s.copy(h = h), predicate, ch.args.toList, ch.argsExp, ch.perm, ch.permExp, InsertionOrderedSet.empty, pve, v, pa)(
      (s1, v1) => Q(s1, s1.h, v1))
  }

  /** Folds the given predicate instance. Before the fold, nested predicate instances required by the
    * predicate's body are folded as well (up to the maximal heuristics depth), if they are not yet held.
    */
  private def foldPredicate(predicate: ast.Predicate,
                            pa: ast.PredicateAccess,
                            tArgs: Seq[Term],
                            eArgs: Option[Seq[ast.Exp]],
                            tPerm: Term,
                            ePerm: Option[ast.Exp])
                           (s: State, h: Heap, v: Verifier)
                           (Q: (State, Heap, Verifier) => VerificationResult)
  : VerificationResult = {

    val pve = HeuristicsFailed(pa)
    val s0 = s.copy(h = h)

    def fold(s1: State, v1: Verifier): VerificationResult =
      predicateSupporter.fold(s1, pa, tArgs.toList, eArgs, tPerm, ePerm, InsertionOrderedSet.empty, pve, v1)(
        (s2, v2) => Q(s2, s2.h, v2))

    if (s0.heuristicsDepth > Verifier.config.maxHeuristicsDepth()) {
      fold(s0, v)
    } else {
      val tArgsWithE =
        if (debugOn) tArgs zip eArgs.get.map(Some(_))
        else tArgs zip Seq.fill(tArgs.length)(None)
      val gIns = s0.g + Store(predicate.formalArgs map (_.localVar) zip tArgsWithE)
      val s1 = s0.copy(g = gIns, heuristicsDepth = s0.heuristicsDepth + 1)

      prepareFold(predicate.body.get.topLevelConjuncts, tPerm, ePerm, pve)(s1, v)((s2, v2) =>
        fold(s2.copy(g = s0.g, heuristicsDepth = s0.heuristicsDepth), v2))
    }
  }

  /* Folds the nested predicate instances required by the given conjuncts of a predicate body, which
   * are evaluated in a store that maps the predicate's formal arguments to the actual arguments.
   */
  private def prepareFold(conjuncts: Seq[ast.Exp], tPerm: Term, ePerm: Option[ast.Exp], pve: PartialVerificationError)
                         (s: State, v: Verifier)
                         (Q: (State, Verifier) => VerificationResult)
  : VerificationResult = {

    if (conjuncts.isEmpty) {
      Q(s, v)
    } else {
      prepareFoldConjunct(conjuncts.head, tPerm, ePerm, pve)(s, v)((s1, v1) =>
        prepareFold(conjuncts.tail, tPerm, ePerm, pve)(s1, v1)(Q))
    }
  }

  private def prepareFoldConjunct(conjunct: ast.Exp, tPerm: Term, ePerm: Option[ast.Exp], pve: PartialVerificationError)
                                 (s: State, v: Verifier)
                                 (Q: (State, Verifier) => VerificationResult)
  : VerificationResult = {

    conjunct match {
      case ast.Implies(left, right) =>
        evaluator.eval(s, left, pve, v)((s1, tLeft, eLeft, v1) =>
          brancher.branch(s1, tLeft, (left, eLeft), v1)(
            (s2, v2) => prepareFold(right.topLevelConjuncts, tPerm, ePerm, pve)(s2, v2)(Q),
            (s2, v2) => Q(s2, v2)))

      case ast.PredicateAccessPredicate(pa, permExp) =>
        val predicate = s.program.findPredicate(pa.predicateName)
        evaluator.evals(s, pa.args, _ => pve, v)((s1, tArgs, eArgs, v1) =>
          evaluator.eval(s1, permExp.getOrElse(ast.FullPerm()()), pve, v1)((s2, tNestedPerm, eNestedPerm, v2) => {
            val alreadyHeld = s2.h.values.exists {
              case ch: BasicChunk => ch.resourceID == PredicateID && ch.id.name == pa.predicateName && ch.args == tArgs
              case _ => false
            }

            if (alreadyHeld || predicate.body.isEmpty) {
              Q(s2, v2)
            } else {
              val tFoldPerm = PermTimes(tNestedPerm, tPerm)
              val eFoldPerm = Option.when(debugOn)(ast.PermMul(eNestedPerm.get, ePerm.get)())

              /* If folding the nested instance fails, we continue without it: the instance might
               * still be available, e.g. via an aliasing chunk, and otherwise the fold fails anyway.
               */
              optionally(s2, v2)((s3, v3, QS) =>
                foldPredicate(predicate, pa, tArgs, eArgs, tFoldPerm, eFoldPerm)(s3, s3.h, v3)((s4, _, v4) =>
                  QS(s4.copy(g = s2.g), v4))
              )(Q)
            }
          }))

      case _ =>
        Q(s, v)
    }
  }

  /* Helpers */

  /* Executes `action`; if it fails before invoking its continuation, Q is invoked on the unchanged state */
  private def optionally(s: State, v: Verifier)
                        (action: (State, Verifier, (State, Verifier) => VerificationResult) => VerificationResult)
                        (Q: (State, Verifier) => VerificationResult)
  : VerificationResult = {

    var reached = false

    v.decider.pushScope()
    val result = action(s, v, (s1, v1) => {
      reached = true
      Q(s1, v1)
    })
    v.decider.popScope()

    if (reached || !result.isFatal) result
    else Q(s, v)
  }

  /* The predicate chunks in `h` whose predicate body mentions the missing resource. Chunks with an argument
   * that also occurs as an argument of the missing resource are returned first, since they are the most
   * likely to provide it.
   */
  private def predicateChunksProviding(s: State, h: Heap, missing: MissingResource): Seq[BasicChunk] = {
    val program = s.program

    val providesMissing: PartialFunction[ast.Node, Any] = {
      case ast.AccessPredicate(locacc: ast.LocationAccess, _) if locacc.loc(program) == missing.resource =>
    }

    val candidates =
      h.values.collect {
        case ch: BasicChunk if ch.resourceID == PredicateID && program.findPredicate(ch.id.name).existsDefined(providesMissing) => ch
      }.toSeq

    candidates.sortBy(ch => if (ch.args.exists(missing.args.contains)) 0 else 1)
  }
}
