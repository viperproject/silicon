package viper
package silicon
package supporters

import com.weiglewilczek.slf4s.Logging
import silver.verifier.PartialVerificationError
import silver.verifier.errors.HeuristicsFailed
import silver.verifier.reasons.{InsufficientPermission, MagicWandChunkNotFound}
import interfaces.{Evaluator, Producer, Consumer, Executor, VerificationResult, Failure}
import interfaces.state.{StateFactory, Chunk, State, PathConditions, Heap, Store, FieldChunk}
import state.{MagicWandChunk, DirectPredicateChunk, DefaultContext}
import state.terms._

trait HeuristicsSupporter[ST <: Store[ST],
                        H <: Heap[H],
                        PC <: PathConditions[PC],
                        S <: State[ST, H, S]]
    { this:      Logging
            with Evaluator[ST, H, S, DefaultContext[H]]
            with Producer[ST, H, S, DefaultContext[H]]
            with Consumer[Chunk, ST, H, S, DefaultContext[H]]
            with Executor[ST, H, S, DefaultContext[H]]
            with MagicWandSupporter[ST, H, PC, S] =>

      protected val stateFactory: StateFactory[ST, H, S]
      import stateFactory._

  protected val config: Config

  object heuristicsSupporter {
    private type C = DefaultContext[H]
    private type CH = Chunk

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

    private def tryWithReactions[O]
                                (description: String)
                                (σ: S, h: H, _c: C)
                                (action: (S, H, C, (O, C) => VerificationResult) => VerificationResult,
                                 initialFailure: Option[Failure[ST, H, S]])
                                (Q: (O, C) => VerificationResult)
                                : VerificationResult = {

      val myId = cnt; cnt += 1
      var printedHeader = false

      def lnsay(msg: String, ident: Int = 1) {
        println()
        say(msg, ident)
      }

      def say(msg: String, ident: Int = 1) {
        if (!printedHeader) {
          println("\n[tryWithReactions]")
          printedHeader = true
        }

        val ws = "  "
        val s1 = if (ident == 0) "" else ws
        val s2 = ws * (ident - 1)
        println(s"$s1($myId)$s2 $msg")
      }

      var localActionSuccess = false
      val c =
        if (_c.triggerAction == null) _c.copy(triggerAction = action)
        else _c

      if (initialFailure.nonEmpty) lnsay(s"retrying $description")

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
            logger.debug("[tryWithReactions] ******************* Heuristics stack grew too large ***************** ")
            Thread.sleep(2500)
          }

        case actionFailure: Failure[ST, H, S] =>
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
            reactionResult = remainingReactions.head.apply(σ, h, c1)((σ1, h1, c2) => {
              say(s"reaction ${triedReactions + 1} locally succeeded")
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

        case reactionFailure: Failure[ST, H, S] =>
          initialFailure.getOrElse(globalActionResult)
      }
    }

    def generateReactions(σ: S, h: H, c: C, cause: Failure[ST, H, S])
                         : Seq[(S, H, C) => ((S, H, C) => VerificationResult) => VerificationResult] = {

      val pve = HeuristicsFailed(ast.True()()) /* TODO: Use a meaningful node */

      def ok(e: ast.Expression) = !e.existsDefined { case lv: ast.LocalVariable if σ.γ.get(lv).isEmpty => }

      /* HS1: Apply/unfold if wand/pred containing missing wand or acc
       * HS2: package/fold missing wand/pred
       * HS3: Apply/unfold all other wands/preds
       */

      cause.message.reason match {
        case reason: MagicWandChunkNotFound =>
          /* HS1 (wands) */
          val wand = reason.offendingNode
          val structureMatcher = matchers.structure(wand, c.program)
          val wandChunks = wandInstancesMatching(σ, h, c, structureMatcher)
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

          /* HS1 (wands) */
          val wandChunks = wandInstancesMatching(σ, h, c, locationMatcher)
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
          val foldPredicateReaction =
            reason.offendingNode match {
              case pa: ast.PredicateAccess if ok(pa) =>
                val acc = ast.PredicateAccessPredicate(pa, ast.FullPerm()())()
                Some(foldPredicate(acc, pve) _)

              case _ => None
            }

          applyWandReactions ++ unfoldPredicateReactions ++ foldPredicateReaction

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
        println(s"  reaction: packaging $wand")
        /* TODO: The next block is an exact copy of the corresponding case in the DefaultConsumer. Reuse code! */
        magicWandSupporter.packageWand(σ \ h, wand, pve, c)((chWand, c1) => {
          val h2 = h + chWand /* h2 = σUsed'' */
          val topReserveHeap = c1.reserveHeaps.head + h2
          val c2 = c1.copy(reserveHeaps = topReserveHeap +: c1.reserveHeaps.drop(2),
                           exhaleExt = c.exhaleExt,
                           lhsHeap = None)
          val σEmp = Σ(σ.γ, H(), σ.g)
          Q(σEmp, σEmp.h, c2)})
//        val packagingExp = ast.Packaging(wand, ast.True()())()
//        consume(σ \ h, p, packagingExp, pve, c)((σ2, _, _, c2) => {
//          Q(σ2, σ2.h, c2)})
      } else {
        println(s"  reaction: package $wand")
        val packageStmt = ast.Package(wand)()
        exec(σ \ h, packageStmt, c)((σ1, c1) => {
          Q(σ1, σ1.h, c1)})
      }
    }

    def applyWand(wand: ast.MagicWand, bindings: Map[ast.Variable, Term], pve: PartialVerificationError)
                 (σ: S, h: H, c: C)
                 (Q: (S, H, C) => VerificationResult)
                 : VerificationResult = {

      /* TODO: Test combination of applyWand-heuristic and wand references (wand w := ...) */

      if (c.exhaleExt) {
        println(s"  reaction: applying $wand")
        val lhsAndWand = ast.And(wand.left, wand)()
        magicWandSupporter.applyingWand(σ \ h, Γ(bindings), wand, lhsAndWand, pve, c)(Q)
      } else {
        println(s"  reaction: apply $wand")
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
        println(s"  reaction: unfolding $acc")
        magicWandSupporter.unfoldingPredicate(σ \ h, acc, pve, c)(Q)
      } else {
        println(s"  reaction: unfold $acc")
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
        println(s"  reaction: folding $acc")
        magicWandSupporter.foldingPredicate(σ \ h, acc, pve, c)(Q)
      } else {
        println(s"  reaction: fold $acc")
        val foldStmt = ast.Fold(acc)()
        exec(σ \ h, foldStmt, c)((σ1, c1) => {
          Q(σ1, σ1.h, c1)})
      }
    }

    /* Helpers */

    def predicateInstancesMatching(σ: S, h: H, c: C, f: PartialFunction[silver.ast.Node, _]): Seq[ast.PredicateAccessPredicate] = {
      val allChunks = σ.h.values ++ h.values ++ c.reserveHeaps.flatMap(_.values)

      val predicateChunks =
        allChunks.collect {
          case ch: DirectPredicateChunk =>
            val body = c.program.findPredicate(ch.name)

            body.existsDefined(f) match {
              case true => Some(ch)
              case _ => None
            }
        }.flatten


      val predicateAccesses =
        predicateChunks.flatMap {
          case DirectPredicateChunk(name, args, _, _, _) =>
            var success = true

            val reversedArgs: Seq[ast.Expression] =
              args map {
                case True() => ast.True()()
                case False() => ast.False()()
                case IntLiteral(n) => ast.IntegerLiteral(n)()
                case t =>
                  σ.γ.values.find(p => p._2 == t).map(_._1)
                      /* Found a local variable v s.t. v |-> t */
                    .orElse(
                      allChunks.collectFirst {
                        case fc: FieldChunk if fc.value == t =>
                          σ.γ.values.find(p => p._2 == fc.args(0))
                                    .map(_._1)
                                    .map(v => ast.FieldAccess(v, c.program.findField(fc.name))())
                      }.flatten
                        /* Found a local variable v and a field f s.t. v.f |-> t */
                    ).getOrElse {
                      success = false
                      ast.True()() /* Dummy value */
                    }
              }

            if (success)
              Some(ast.PredicateAccessPredicate(ast.PredicateAccess(reversedArgs, c.program.findPredicate(name))(), ast.FullPerm()())())
            else
              None
        }.toSeq

      predicateAccesses
    }

    def wandInstancesMatching(σ: S, h: H, c: C, f: PartialFunction[silver.ast.Node, _]): Seq[MagicWandChunk] = {
      val allChunks = σ.h.values ++ h.values ++ c.reserveHeaps.flatMap(_.values)

      val wands =
        allChunks.collect {
          case ch: MagicWandChunk =>
            ch.ghostFreeWand.right.existsDefined(f) match {
              case true => Some(ch)
              case _ => None
            }
        }.flatten.toSeq

      wands
    }

    object matchers {
      def location(loc: ast.Location, program: ast.Program): PartialFunction[silver.ast.Node, Any] = {
        case ast.AccessPredicate(locacc: ast.LocationAccess, _) if locacc.loc(program) == loc =>
      }

      def structure(wand: ast.MagicWand, program: ast.Program): PartialFunction[silver.ast.Node, Any] = {
        case other: ast.MagicWand if wand.structurallyMatches(other, program) =>
      }
    }
  }
}
