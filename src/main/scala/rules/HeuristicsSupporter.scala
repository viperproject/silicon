/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.rules

import viper.silver.ast
import viper.silver.verifier.PartialVerificationError
import viper.silver.verifier.errors.HeuristicsFailed
import viper.silver.verifier.reasons.{InsufficientPermission, MagicWandChunkNotFound}
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.interfaces._
import viper.silicon.interfaces.state._
import viper.silicon.resources.{FieldID, PredicateID}
import viper.silicon.state._
import viper.silicon.state.terms._
import viper.silicon.verifier.Verifier

object heuristicsSupporter extends SymbolicExecutionRules with Immutable {
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

  @inline
  def tryOperation[O1, O2, O3]
                  (description: String)
                  (s: State, h: Heap, v: Verifier)
                  (action: (State, Heap, Verifier, (State, O1, O2, O3, Verifier) => VerificationResult) => VerificationResult)
                  (Q: (State, O1, O2, O3, Verifier) => VerificationResult)
                  : VerificationResult = {

    val tupledAction = (s1: State, h1: Heap, v1: Verifier, QS: (State, (O1, O2, O3), Verifier) => VerificationResult) =>
        action(s1, h1, v1, (s2, o1: O1, o2: O2, o3: O3, v2) => QS(s2, (o1, o2, o3), v2))

    val tupledQ = (s1: State, os: (O1, O2, O3), v1: Verifier) => Q(s1, os._1, os._2, os._3, v1)

    tryWithReactions[(O1, O2, O3)](description)(s, h, v)(tupledAction, None)(tupledQ)
  }

  @inline
  def tryOperation[O1, O2, O3, O4]
                  (description: String)
                  (s: State, h: Heap, v: Verifier)
                  (action: (State, Heap, Verifier, (State, O1, O2, O3, O4, Verifier) => VerificationResult) => VerificationResult)
                  (Q: (State, O1, O2, O3, O4, Verifier) => VerificationResult)
                  : VerificationResult = {

    val tupledAction = (s1: State, h1: Heap, v1: Verifier, QS: (State, (O1, O2, O3, O4), Verifier) => VerificationResult) =>
      action(s1, h1, v1, (s2, o1: O1, o2: O2, o3: O3, o4: O4, v2) => QS(s2, (o1, o2, o3, o4), v2))

    val tupledQ = (s1: State, os: (O1, O2, O3, O4), v1: Verifier) => Q(s1, os._1, os._2, os._3, os._4, v1)

    tryWithReactions[(O1, O2, O3, O4)](description)(s, h, v)(tupledAction, None)(tupledQ)
  }

  /* tryWithReactions, which executes the action-reaction cycle */

//  private var cnt = 0L
//  private var stack = Stack[Long]()
//  private val heuristicsLogger = LoggerFactory.getLogger("heuristics")

  private def tryWithReactions[O]
                              (description: String)
                              (_s: State, h: Heap, v: Verifier)
                              (action: (State, Heap, Verifier, (State, O, Verifier) => VerificationResult) => VerificationResult,
                               initialFailure: Option[Failure])
                              (Q: (State, O, Verifier) => VerificationResult)
                              : VerificationResult = {

//    val myId = cnt; cnt += 1
//    val baseIdent = "  "
//    var printedHeader = false
//
//    def lnsay(msg: String, ident: Int = 1) {
//      val prefix = "\n" + (if (ident == 0) "" else baseIdent)
//      dosay(prefix, msg, ident - 1)
//    }
//
//    def say(msg: String, ident: Int = 1) {
//      val prefix = if (ident == 0) "" else baseIdent
//      dosay(prefix, msg, ident - 1)
//    }
//
//    def dosay(prefix: String, msg: String, ident: Int) {
//      if (!printedHeader) {
//        heuristicsLogger.debug("\n[tryWithReactions]")
//        printedHeader = true
//      }
//
//      val messagePrefix = baseIdent * ident
//      heuristicsLogger.debug(s"$prefix($myId)$messagePrefix $msg")
//    }

    var localActionSuccess = false
    val s =
      if (_s.triggerAction == null) _s.copy(triggerAction = action)
      else _s

//    if (initialFailure.nonEmpty) {
//      lnsay(s"retrying $description")
//      say(s"s.h = ${σ.h}")
//      say(s"h = $h")
//      say(s"c.reserveHeaps:")
//      c.reserveHeaps.map(stateFormatter.format).foreach(str => say(str, 2))
//    }

    val globalActionResult =
      action(s, h, v, (s1, outputs, v1) => {
        /* We are here if the `action` invoked the success continuation `QS` */
        localActionSuccess = true
//        if (initialFailure.nonEmpty) say(s"$description succeeded locally")
        val s2 =
          if (action.eq(s1.triggerAction))
            s1.copy(triggerAction = null, heuristicsDepth = 0)
          else
            s1
          /* TODO: depth may only be reset if this action is not part of the
           *       execution of a reaction. I don't (yet) know how to detect
           *       this, though ...
           */
//          stack = stack.tail
        Q(s2, outputs, v1)})

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

    globalActionResult match {
      case _ if    localActionSuccess
                || !globalActionResult.isFatal
                || !s.applyHeuristics
//                || stack.size >= 10 * config.maxHeuristicsDepth() /* TODO: Ugly hack! Shouldn't be necessary */
                || s.heuristicsDepth >= Verifier.config.maxHeuristicsDepth() => /* Quit trying heuristics */

//        /* TODO: Remove */
//        if (stack.size >= 10 * config.maxHeuristicsDepth()) {
//          log.debug("[tryWithReactions] ******************* Heuristics stack grew too large ***************** ")
////            Thread.sleep(2500)
//        }

      case actionFailure: Failure =>
//        stack ::= myId

//        say(s"action $myId failed (locally and globally)")
//        say(s"description = $description")
//        say(s"globalActionResult = $globalActionResult")
//        say(s"stack = $stack")
//        say("context:")
//        say(s"depth = ${c.heuristicsDepth}", 2)
//        say(s"applyHeuristics = ${c.applyHeuristics}", 2)
//        say(s"exhaleExt = ${c.exhaleExt}", 2)

        var remainingReactions = generateReactions(s, h, v, actionFailure)
        var triedReactions = 0

//        say(s"generated ${remainingReactions.length} possible reactions")

        while (reactionResult.isFatal && remainingReactions.nonEmpty) {
//          lnsay(s"trying next reaction (${triedReactions + 1} out of ${triedReactions + remainingReactions.length})")

          val s1 = s.copy(h = h,
                          heuristicsDepth = s.heuristicsDepth + 1)
//          bookkeeper.appliedHeuristicReactions += 1

          reactionResult =
            heuristicsSupporter.tryOperation[Heap](s"applying heuristic")(s1, h, v)((s1, h1, v1, QS) =>
              remainingReactions.head.apply(s1, h1, v1)((s2, h2, v2) => {
//                say(s"reaction ${triedReactions + 1} locally succeeded")
//                say(s"s2.h = ${σ2.h}")
//                say(s"h2 = $h2")
//                say(s"c3.reserveHeaps:")
//                c3.reserveHeaps.map(stateFormatter.format).foreach(str => say(str, 2))
                QS(s2, h2, v2)})
            )((σ1, h1, c2) => {
                tryWithReactions(description)(σ1, h1, c2)(action, initialFailure.orElse(Some(actionFailure)))(Q)})

//          lnsay(s"returned from reaction ${triedReactions + 1} (out of ${triedReactions + remainingReactions.length})")
//          say(s"reactionResult = $reactionResult")

          triedReactions += 1

          remainingReactions = remainingReactions.tail
        }

//        stack = stack.tail
//
//        lnsay(s"existing tryWithReactions")
//        say(s"localActionSuccess = $localActionSuccess")
//        say(s"reactionResult = $reactionResult")
    }

    reactionResult match {
      case _ if !reactionResult.isFatal =>
        reactionResult

      case _: Failure =>
        initialFailure.getOrElse(globalActionResult)
    }
  }

  def generateReactions(s: State, h: Heap, v: Verifier, cause: Failure)
                       : Seq[(State, Heap, Verifier) => ((State, Heap, Verifier) => VerificationResult) => VerificationResult] = {

    val pve = HeuristicsFailed(ast.TrueLit()()) /* TODO: Use a meaningful node */

    def ok(e: ast.Exp) = !e.existsDefined { case lv: ast.AbstractLocalVar if s.g.get(lv).isEmpty => }

    /* HS1: Apply/unfold if wand/pred containing missing wand or acc
     * HS2: package/fold missing wand/pred
     * HS3: Apply/unfold all other wands/preds
     */

    cause.message.reason match {
      case reason: MagicWandChunkNotFound =>
        val chunks = (s.h.values ++ h.values ++ s.reserveHeaps.flatMap(_.values)).toSeq.distinct

        /* HS1 (wands) */
        val wand = reason.offendingNode
        val structureMatcher = matchers.structure(wand, Verifier.program)
        val wandChunks = wandInstancesMatching(chunks, structureMatcher)
        val applyWandReactions = wandChunks flatMap {
          case ch if ok(ch.id.ghostFreeWand) => Some(applyWand(ch.id.ghostFreeWand, ch.bindings, pve) _)
          case _ => None
        }

        /* HS2 */
        val packageReaction =
          if (ok(wand)) Some(packageWand(wand, pve) _)
          else None

        applyWandReactions ++ packageReaction

      case reason: InsufficientPermission =>
        val locationMatcher = matchers.location(reason.offendingNode.loc(Verifier.program), Verifier.program)
        val chunks = (s.h.values ++ h.values ++ s.reserveHeaps.flatMap(_.values)).toSeq.distinct

        /* HS1 (wands) */
        val wandChunks = wandInstancesMatching(chunks, locationMatcher)
        val applyWandReactions = wandChunks flatMap {
          case ch if ok(ch.id.ghostFreeWand) => Some(applyWand(ch.id.ghostFreeWand, ch.bindings, pve) _)
          case _ => None
        }

        /* HS1 (predicates) */
        val predicateAccesses = predicateInstancesMatching(s, h, v, locationMatcher)
        val unfoldPredicateReactions = predicateAccesses flatMap {
          case acc if ok(acc) => Some(unfoldPredicate(acc, pve) _)
          case _ => None
        }

        /* HS2 (predicates) */
        val foldPredicateReactions =
          reason.offendingNode match {
            case pa: ast.PredicateAccess if ok(pa) =>
              val foldMissing = foldPredicate(ast.PredicateAccessPredicate(pa, ast.FullPerm()())(), pve) _

              val optFoldLoad =
                cause.load match {
                  case Some(ts) =>
                    assert(pa.args.length == ts.length)
                    Some(foldPredicate(Verifier.program.findPredicate(pa.predicateName), ts.toList, FullPerm(), pve) _)

                  case _ => None
                }

              optFoldLoad.toSeq :+ foldMissing

            case _ => Nil
          }

        applyWandReactions ++ unfoldPredicateReactions ++ foldPredicateReactions

      case _ => Nil
    }
  }

  /* Heuristics */

  def packageWand(wand: ast.MagicWand, pve: PartialVerificationError)
                 (s: State, h: Heap, v: Verifier)
                 (Q: (State, Heap, Verifier) => VerificationResult)
                 : VerificationResult = {
      val packageStmt = ast.Package(wand, ast.Seqn(Seq(), Seq())())()
      exec(s.copy(h = h), packageStmt, v)((s1, v1) => {
        Q(s1, s1.h, v1)})
  }

  def applyWand(wand: ast.MagicWand, bindings: Map[ast.AbstractLocalVar, Term], pve: PartialVerificationError)
               (s: State, h: Heap, v: Verifier)
               (Q: (State, Heap, Verifier) => VerificationResult)
               : VerificationResult = {

      val applyStmt = ast.Apply(wand)()
      exec(s.copy(g = Store(bindings), h = h), applyStmt, v)((s1, v1) => {
        Q(s1.copy(g = s.g), s1.h, v1)})
  }

  def unfoldPredicate(acc: ast.PredicateAccessPredicate, pve: PartialVerificationError)
                     (s: State, h: Heap, v: Verifier)
                     (Q: (State, Heap, Verifier) => VerificationResult)
                     : VerificationResult = {
      val unfoldStmt = ast.Unfold(acc)()
      exec(s.copy(h = h), unfoldStmt, v)((s1, v1) => {
        Q(s1, s1.h, v1)})
  }

  def foldPredicate(acc: ast.PredicateAccessPredicate, pve: PartialVerificationError)
                   (s: State, h: Heap, v: Verifier)
                   (Q: (State, Heap, Verifier) => VerificationResult)
                   : VerificationResult = {
      val foldStmt = ast.Fold(acc)()
      exec(s.copy(h = h), foldStmt, v)((s1, v1) => {
        Q(s1, s1.h, v1)})
  }

  def foldPredicate(predicate: ast.Predicate, tArgs: List[Term], tPerm: Term, pve: PartialVerificationError)
                   (s: State, h: Heap, v: Verifier)
                   (Q: (State, Heap, Verifier) => VerificationResult)
                   : VerificationResult = {
    predicateSupporter.fold(s.copy(h = h), predicate, tArgs, tPerm, InsertionOrderedSet.empty, pve, v)((s1, v1) =>
        Q(s1, s1.h, v1))
  }

  /* Helpers */

  def predicateInstancesMatching(s: State, h: Heap, v: Verifier, f: PartialFunction[ast.Node, _]): Seq[ast.PredicateAccessPredicate] = {
    val allChunks = s.h.values ++ h.values ++ s.reserveHeaps.flatMap(_.values)
    val program = Verifier.program

    val predicateChunks =
      allChunks.collect {
        case ch: BasicChunk if ch.resourceID == PredicateID() =>
          val body = program.findPredicate(ch.id.name)

          if (body.existsDefined(f)) {
            Some(ch)
          } else {
            None
          }
      }.flatten

    val predicateAccesses =
      predicateChunks.flatMap {
        case BasicChunk(PredicateID(), BasicChunkIdentifier(name), args, _, _) =>
          val reversedArgs: Seq[ast.Exp] = backtranslate(s.g.values, allChunks.toSeq, args, program)

          if (args.length == reversedArgs.length)
            Some(ast.PredicateAccessPredicate(ast.PredicateAccess(reversedArgs, name)(), ast.FullPerm()())())
          else
            None
      }.toSeq

    predicateAccesses
  }

  def wandInstancesMatching(chunks: Seq[Chunk], f: PartialFunction[ast.Node, _]): Seq[MagicWandChunk] = {
    val wands =
      chunks.collect {
        case ch: MagicWandChunk =>
          if (ch.id.ghostFreeWand.right.existsDefined(f)) {
            Some(ch)
          } else {
            None
          }
      }.flatten

    wands
  }

  object matchers {
    def location(loc: ast.Location, program: ast.Program): PartialFunction[ast.Node, Any] = {
      case ast.AccessPredicate(locacc: ast.LocationAccess, _) if locacc.loc(program) == loc =>
    }

    def structure(wand: ast.MagicWand, program: ast.Program): PartialFunction[ast.Node, Any] = {
      case other: ast.MagicWand if MagicWandIdentifier(wand, Verifier.program) == MagicWandIdentifier(other, Verifier.program) =>
    }
  }

  private def backtranslate(bindings: Map[ast.AbstractLocalVar, Term], chunks: Seq[Chunk], ts: Seq[Term], program: ast.Program)
                           : Seq[ast.Exp] = {

    val optEs =
      ts map {
        case True() => Some(ast.TrueLit()())
        case False() => Some(ast.FalseLit()())
        case IntLiteral(n) => Some(ast.IntLit(n)())
        case t =>
          bindings.find(p => p._2 == t).map(_._1)
                    /* Found a local variable v s.t. v |-> t */
                  .orElse(
                    chunks.collectFirst {
                      case fc: BasicChunk if fc.resourceID == FieldID() && fc.snap == t =>
                        bindings.find(p => p._2 == fc.args.head)
                                .map(_._1)
                                .map(v => ast.FieldAccess(v, program.findField(fc.id.name))())
                    }.flatten)
                    /* Found a local variable v and a field f s.t. v.f |-> t */
      }

    optEs.flatten
  }
}
