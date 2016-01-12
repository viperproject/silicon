/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.supporters

import org.slf4s.{LoggerFactory, Logging}
import viper.silver.ast
import viper.silver.verifier.PartialVerificationError
import viper.silver.verifier.errors.HeuristicsFailed
import viper.silver.verifier.reasons.{InsufficientPermission, MagicWandChunkNotFound}
import viper.silicon.{Config, Stack}
import viper.silicon.interfaces._
import viper.silicon.interfaces.state._
import viper.silicon.state.{FieldChunk, MagicWandChunk, PredicateChunk, DefaultContext}
import viper.silicon.state.terms._
import viper.silicon.reporting.Bookkeeper

trait HeuristicsSupporter[ST <: Store[ST],
                        H <: Heap[H],
                        S <: State[ST, H, S]]
    { this:      Logging
            with Evaluator[ST, H, S, DefaultContext[H]]
            with Producer[ST, H, S, DefaultContext[H]]
            with Consumer[ST, H, S, DefaultContext[H]]
            with Executor[ST, H, S, DefaultContext[H]]
            with MagicWandSupporter[ST, H, S] =>

  private[this] type C = DefaultContext[H]

  protected val stateFactory: StateFactory[ST, H, S]
  protected val config: Config
  protected val bookkeeper: Bookkeeper
  protected val predicateSupporter: PredicateSupporter[ST, H, S, C]

  import stateFactory._

  object heuristicsSupporter {

    /* tryOperation-Methods with varying output arity */

    @inline
    def tryOperation[O1, O2]
                    (description: String)
                    (σ: S, h: H, c: C)
                    (action: (S, H, C, (O1, O2, C) => VerificationResult) => VerificationResult)
                    (Q: (O1, O2, C) => VerificationResult)
                    : VerificationResult = {

      val tupledAction = (σ1: S, h1: H, c1: C, QS: ((O1, O2), C) => VerificationResult) =>
        action(σ1, h1, c1, (o1: O1, o2: O2, c2) => QS((o1, o2), c2))

      val tupledQ = (os: (O1, O2), c1: C) => Q(os._1, os._2, c1)

      tryWithReactions[(O1, O2)](description)(σ, h, c)(tupledAction, None)(tupledQ)
    }

    @inline
    def tryOperation[O1, O2, O3]
                    (description: String)
                    (σ: S, h: H, c: C)
                    (action: (S, H, C, (O1, O2, O3, C) => VerificationResult) => VerificationResult)
                    (Q: (O1, O2, O3, C) => VerificationResult)
                    : VerificationResult = {

      val tupledAction = (σ1: S, h1: H, c1: C, QS: ((O1, O2, O3), C) => VerificationResult) =>
          action(σ1, h1, c1, (o1: O1, o2: O2, o3: O3, c2) => QS((o1, o2, o3), c2))

      val tupledQ = (os: (O1, O2, O3), c1: C) => Q(os._1, os._2, os._3, c1)

      tryWithReactions[(O1, O2, O3)](description)(σ, h, c)(tupledAction, None)(tupledQ)
    }

    @inline
    def tryOperation[O1, O2, O3, O4]
                    (description: String)
                    (σ: S, h: H, c: C)
                    (action: (S, H, C, (O1, O2, O3, O4, C) => VerificationResult) => VerificationResult)
                    (Q: (O1, O2, O3, O4, C) => VerificationResult)
                    : VerificationResult = {

      val tupledAction = (σ1: S, h1: H, c1: C, QS: ((O1, O2, O3, O4), C) => VerificationResult) =>
        action(σ1, h1, c1, (o1: O1, o2: O2, o3: O3, o4: O4, c2) => QS((o1, o2, o3, o4), c2))

      val tupledQ = (os: (O1, O2, O3, O4), c1: C) => Q(os._1, os._2, os._3, os._4, c1)

      tryWithReactions[(O1, O2, O3, O4)](description)(σ, h, c)(tupledAction, None)(tupledQ)
    }

    /* tryWithReactions, which executes the action-reaction cycle */

    private var cnt = 0L
    private var stack = Stack[Long]()
    private val heuristicsLogger = LoggerFactory.getLogger("heuristics")

    private def tryWithReactions[O]
                                (description: String)
                                (σ: S, h: H, _c: C)
                                (action: (S, H, C, (O, C) => VerificationResult) => VerificationResult,
                                 initialFailure: Option[Failure])
                                (Q: (O, C) => VerificationResult)
                                : VerificationResult = {

      val myId = cnt; cnt += 1
      val baseIdent = "  "
      var printedHeader = false

      def lnsay(msg: String, ident: Int = 1) {
        val prefix = "\n" + (if (ident == 0) "" else baseIdent)
        dosay(prefix, msg, ident - 1)
      }

      def say(msg: String, ident: Int = 1) {
        val prefix = if (ident == 0) "" else baseIdent
        dosay(prefix, msg, ident - 1)
      }

      def dosay(prefix: String, msg: String, ident: Int) {
        if (!printedHeader) {
          heuristicsLogger.debug("\n[tryWithReactions]")
          printedHeader = true
        }

        val messagePrefix = baseIdent * ident
        heuristicsLogger.debug(s"$prefix($myId)$messagePrefix $msg")
      }

      var localActionSuccess = false
      val c =
        if (_c.triggerAction == null) _c.copy(triggerAction = action)
        else _c

      if (initialFailure.nonEmpty) {
        lnsay(s"retrying $description")
        say(s"s.h = ${σ.h}")
        say(s"h = $h")
        say(s"c.reserveHeaps:")
        c.reserveHeaps.map(stateFormatter.format).foreach(str => say(str, 2))
      }

      val globalActionResult =
        action(σ, h, c, (outputs, c1) => {
          /* We are here if the `action` invoked the success continuation `QS` */
          localActionSuccess = true
          if (initialFailure.nonEmpty) say(s"$description succeeded locally")
          val c2 =
            if (action.eq(c1.triggerAction))
              c1.copy(triggerAction = null, heuristicsDepth = 0)
            else
              c1
            /* TODO: depth may only be reset if this action is not part of the
             *       execution of a reaction. I don't (yet) know how to detect
             *       this, though ...
             */
//          stack = stack.tail
          Q(outputs, c2)})

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
                  || !c.applyHeuristics
                  || stack.size >= 10 * config.maxHeuristicsDepth() /* TODO: Ugly hack! Shouldn't be necessary */
                  || c.heuristicsDepth >= config.maxHeuristicsDepth() => /* Quit trying heuristics */

          /* TODO: Remove */
          if (stack.size >= 10 * config.maxHeuristicsDepth()) {
            log.debug("[tryWithReactions] ******************* Heuristics stack grew too large ***************** ")
//            Thread.sleep(2500)
          }

        case actionFailure: Failure =>
          stack ::= myId

          say(s"action $myId failed (locally and globally)")
          say(s"description = $description")
          say(s"globalActionResult = $globalActionResult")
          say(s"stack = $stack")
          say("context:")
          say(s"depth = ${c.heuristicsDepth}", 2)
          say(s"applyHeuristics = ${c.applyHeuristics}", 2)
          say(s"exhaleExt = ${c.exhaleExt}", 2)
//          Thread.sleep(500)

          var remainingReactions = generateReactions(σ, h, c, actionFailure)
          var triedReactions = 0

          say(s"generated ${remainingReactions.length} possible reactions")

          while (reactionResult.isFatal && remainingReactions.nonEmpty) {
            lnsay(s"trying next reaction (${triedReactions + 1} out of ${triedReactions + remainingReactions.length})")

            val c1 = c.copy(heuristicsDepth = c.heuristicsDepth + 1)
            bookkeeper.appliedHeuristicReactions += 1

            reactionResult =
              heuristicsSupporter.tryOperation[S, H](s"applying heuristic ($myId)")(σ \ h, h, c1)((σ1, h1, c2, QS) =>
                remainingReactions.head.apply(σ1, h1, c2)((σ2, h2, c3) => {
                  say(s"reaction ${triedReactions + 1} locally succeeded")
                  say(s"s2.h = ${σ2.h}")
                  say(s"h2 = $h2")
                  say(s"c3.reserveHeaps:")
                  c3.reserveHeaps.map(stateFormatter.format).foreach(str => say(str, 2))
                  QS(σ2, h2, c3)})
              )((σ1, h1, c2) => {
                  tryWithReactions(description)(σ1, h1, c2)(action, initialFailure.orElse(Some(actionFailure)))(Q)})

            lnsay(s"returned from reaction ${triedReactions + 1} (out of ${triedReactions + remainingReactions.length})")
            say(s"reactionResult = $reactionResult")

            triedReactions += 1

            remainingReactions = remainingReactions.tail
          }

          stack = stack.tail

          lnsay(s"existing tryWithReactions")
          say(s"localActionSuccess = $localActionSuccess")
          say(s"reactionResult = $reactionResult")
      }

      reactionResult match {
        case _ if !reactionResult.isFatal =>
          reactionResult

        case reactionFailure: Failure =>
          initialFailure.getOrElse(globalActionResult)
      }
    }

    def generateReactions(σ: S, h: H, c: C, cause: Failure)
                         : Seq[(S, H, C) => ((S, H, C) => VerificationResult) => VerificationResult] = {

      val pve = HeuristicsFailed(ast.TrueLit()()) /* TODO: Use a meaningful node */

      def ok(e: ast.Exp) = !e.existsDefined { case lv: ast.AbstractLocalVar if σ.γ.get(lv).isEmpty => }

      /* HS1: Apply/unfold if wand/pred containing missing wand or acc
       * HS2: package/fold missing wand/pred
       * HS3: Apply/unfold all other wands/preds
       */

      cause.message.reason match {
        case reason: MagicWandChunkNotFound =>
          val chunks = (σ.h.values ++ h.values ++ c.reserveHeaps.flatMap(_.values)).toSeq

          /* HS1 (wands) */
          val wand = reason.offendingNode
          val structureMatcher = matchers.structure(wand, c.program)
          val wandChunks = wandInstancesMatching(chunks, structureMatcher)
          val applyWandReactions = wandChunks flatMap {
            case ch if ok(ch.ghostFreeWand) => Some(applyWand(ch.ghostFreeWand, ch.bindings, pve) _)
            case _ => None
          }

          /* HS2 */
          val packageReaction =
            if (ok(wand)) Some(packageWand(wand, pve) _)
            else None

          applyWandReactions ++ packageReaction

        case reason: InsufficientPermission =>
          val locationMatcher = matchers.location(reason.offendingNode.loc(c.program), c.program)
          val chunks = (σ.h.values ++ h.values ++ c.reserveHeaps.flatMap(_.values)).toSeq

          /* HS1 (wands) */
          val wandChunks = wandInstancesMatching(chunks, locationMatcher)
          val applyWandReactions = wandChunks flatMap {
            case ch if ok(ch.ghostFreeWand) => Some(applyWand(ch.ghostFreeWand, ch.bindings, pve) _)
            case _ => None
          }

          /* HS1 (predicates) */
          val predicateAccesses = predicateInstancesMatching(σ, h, c, locationMatcher)
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
                      Some(foldPredicate(c.program.findPredicate(pa.predicateName), ts.toList, FullPerm(), pve) _)

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
                   (σ: S, h: H, c: C)
                   (Q: (S, H, C) => VerificationResult)
                   : VerificationResult = {

      val p = FullPerm()

      if (c.exhaleExt) {
        heuristicsLogger.debug(s"  reaction: packaging $wand")
        /* TODO: The next block is an exact copy of the corresponding case in the DefaultConsumer. Reuse code! */
        magicWandSupporter.packageWand(σ \ h, wand, pve, c)((chWand, c1) => {
          val h2 = h + chWand /* h2 = σUsed'' */
          val topReserveHeap = c1.reserveHeaps.head + h2
          val c2 = c1.copy(reserveHeaps = topReserveHeap +: c1.reserveHeaps.drop(2),
                           lhsHeap = None,
                           exhaleExt = c.exhaleExt,
                           consumedChunks = Nil +: c1.consumedChunks.drop(2))
          val σEmp = Σ(σ.γ, H(), σ.g)
          Q(σEmp, σEmp.h, c2)})
      } else {
        heuristicsLogger.debug(s"  reaction: package $wand")
        val packageStmt = ast.Package(wand)()
        exec(σ \ h, packageStmt, c)((σ1, c1) => {
          Q(σ1, σ1.h, c1)})
      }
    }

    def applyWand(wand: ast.MagicWand, bindings: Map[ast.AbstractLocalVar, Term], pve: PartialVerificationError)
                 (σ: S, h: H, c: C)
                 (Q: (S, H, C) => VerificationResult)
                 : VerificationResult = {

      /* TODO: Test combination of applyWand-heuristic and wand references (wand w := ...) */

      if (c.exhaleExt) {
        heuristicsLogger.debug(s"  reaction: applying $wand")
        val lhsAndWand = ast.And(wand.left, wand)()
        magicWandSupporter.applyingWand(σ \ h, Γ(bindings), wand, lhsAndWand, pve, c)(Q)
      } else {
        heuristicsLogger.debug(s"  reaction: apply $wand")
        val applyStmt = ast.Apply(wand)()
        exec(σ \ h \ Γ(bindings), applyStmt, c)((σ1, c1) => {
          Q(σ1 \ σ.γ, σ1.h, c1)})
      }
    }

    def unfoldPredicate(acc: ast.PredicateAccessPredicate, pve: PartialVerificationError)
                       (σ: S, h: H, c: C)
                       (Q: (S, H, C) => VerificationResult)
                       : VerificationResult = {


      if (c.exhaleExt) {
        heuristicsLogger.debug(s"  reaction: unfolding $acc")
        magicWandSupporter.unfoldingPredicate(σ \ h, acc, pve, c)(Q)
      } else {
        heuristicsLogger.debug(s"  reaction: unfold $acc")
        val unfoldStmt = ast.Unfold(acc)()
        exec(σ \ h, unfoldStmt, c)((σ1, c1) => {
          Q(σ1, σ1.h, c1)})
      }
    }

    def foldPredicate(acc: ast.PredicateAccessPredicate, pve: PartialVerificationError)
                     (σ: S, h: H, c: C)
                     (Q: (S, H, C) => VerificationResult)
                     : VerificationResult = {

      if (c.exhaleExt) {
        heuristicsLogger.debug(s"  reaction: folding $acc")
        magicWandSupporter.foldingPredicate(σ \ h, acc, pve, c)(Q)
      } else {
        heuristicsLogger.debug(s"  reaction: fold $acc")
        val foldStmt = ast.Fold(acc)()
        exec(σ \ h, foldStmt, c)((σ1, c1) => {
          Q(σ1, σ1.h, c1)})
      }
    }

    def foldPredicate(predicate: ast.Predicate, tArgs: List[Term], tPerm: Term, pve: PartialVerificationError)
                     (σ: S, h: H, c: C)
                     (Q: (S, H, C) => VerificationResult)
                     : VerificationResult = {

      if (c.exhaleExt) {
        heuristicsLogger.debug(s"  reaction: folding ${predicate.name}(${tArgs.mkString(",")})")
        magicWandSupporter.foldingPredicate(σ \ h, predicate, tArgs, tPerm, pve, c)(Q)
      } else {
        heuristicsLogger.debug(s"  reaction: fold ${predicate.name}(${tArgs.mkString(",")})")
        predicateSupporter.fold(σ \ h, predicate, tArgs, tPerm, pve, c)((σ1, c1) =>
          Q(σ1, σ1.h, c1))
      }
    }

    /* Helpers */

    def predicateInstancesMatching(σ: S, h: H, c: C, f: PartialFunction[ast.Node, _]): Seq[ast.PredicateAccessPredicate] = {
      val allChunks = σ.h.values ++ h.values ++ c.reserveHeaps.flatMap(_.values)

      val predicateChunks =
        allChunks.collect {
          case ch: PredicateChunk =>
            val body = c.program.findPredicate(ch.name)

            body.existsDefined(f) match {
              case true => Some(ch)
              case _ => None
            }
        }.flatten


      val predicateAccesses =
        predicateChunks.flatMap {
          case PredicateChunk(name, args, _, _) =>
            val reversedArgs: Seq[ast.Exp] = backtranslate(σ.γ.values, allChunks.toSeq, args, c.program)

            if (args.length == reversedArgs.length)
              Some(ast.PredicateAccessPredicate(ast.PredicateAccess(reversedArgs, c.program.findPredicate(name))(), ast.FullPerm()())())
            else
              None
        }.toSeq

      predicateAccesses
    }

    def wandInstancesMatching(chunks: Seq[Chunk], f: PartialFunction[ast.Node, _]): Seq[MagicWandChunk] = {
      val wands =
        chunks.collect {
          case ch: MagicWandChunk =>
            ch.ghostFreeWand.right.existsDefined(f) match {
              case true => Some(ch)
              case _ => None
            }
        }.flatten

      wands
    }

    object matchers {
      def location(loc: ast.Location, program: ast.Program): PartialFunction[ast.Node, Any] = {
        case ast.AccessPredicate(locacc: ast.LocationAccess, _) if locacc.loc(program) == loc =>
      }

      def structure(wand: ast.MagicWand, program: ast.Program): PartialFunction[ast.Node, Any] = {
        case other: ast.MagicWand if wand.structurallyMatches(other, program) =>
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
                        case fc: FieldChunk if fc.snap == t =>
                          bindings.find(p => p._2 == fc.args.head)
                                  .map(_._1)
                                  .map(v => ast.FieldAccess(v, program.findField(fc.name))())
                      }.flatten)
                      /* Found a local variable v and a field f s.t. v.f |-> t */
        }

      optEs.flatten
    }
  }
}
