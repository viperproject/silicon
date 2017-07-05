/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.rules

import viper.silicon.interfaces._
import viper.silicon.interfaces.state._
import viper.silicon.resources.{PropertyInterpreter, Resources}
import viper.silicon.state._
import viper.silicon.state.terms._
import viper.silicon.state.terms.perms.{IsNonPositive, IsPositive}
import viper.silicon.supporters.functions.NoopFunctionRecorder
import viper.silicon.verifier.Verifier
import viper.silver.ast
import viper.silver.verifier.PartialVerificationError
import viper.silver.verifier.reasons.InsufficientPermission

import scala.collection.mutable.ListBuffer

trait ChunkSupportRules extends SymbolicExecutionRules {
  def consume(s: State,
              h: Heap,
              name: String,
              args: Seq[Term],
              perms: Term,
              pve: PartialVerificationError,
              v: Verifier,
              locacc: ast.LocationAccess,
              optNode: Option[ast.Node with ast.Positioned] = None)
             (Q: (State, Heap, Term, Verifier) => VerificationResult)
             : VerificationResult

  def withChunk(s: State,
                h: Heap,
                name: String,
                args: Seq[Term],
                locacc: ast.LocationAccess,
                pve: PartialVerificationError,
                v: Verifier)
               (Q: (State, Heap, BasicChunk, Verifier) => VerificationResult)
               : VerificationResult

  def withChunk(s: State,
                h: Heap,
                name: String,
                args: Seq[Term],
                optPerms: Option[Term],
                locacc: ast.LocationAccess,
                pve: PartialVerificationError,
                v: Verifier)
               (Q: (State, Heap, BasicChunk, Verifier) => VerificationResult)
               : VerificationResult

  def withChunk(s: State,
                name: String,
                args: Seq[Term],
                locacc: ast.LocationAccess,
                pve: PartialVerificationError,
                v: Verifier)
               (Q: (State, BasicChunk, Verifier) => VerificationResult)
               : VerificationResult

  def withChunk(s: State,
                name: String,
                args: Seq[Term],
                optPerms: Option[Term],
                locacc: ast.LocationAccess,
                pve: PartialVerificationError,
                v: Verifier)
               (Q: (State, BasicChunk, Verifier) => VerificationResult)
               : VerificationResult

}

object chunkSupporter extends ChunkSupportRules with Immutable {
  def consume(s: State,
              h: Heap,
              name: String,
              args: Seq[Term],
              perms: Term,
              pve: PartialVerificationError,
              v: Verifier,
              locacc: ast.LocationAccess,
              optNode: Option[ast.Node with ast.Positioned] = None)
             (Q: (State, Heap, Term, Verifier) => VerificationResult)
             : VerificationResult = {

    val description = optNode.orElse(Some(locacc)).map(node => s"consume ${node.pos}: $node").get
//      val description = optNode match {
//        case Some(node) => s"consume ${node.pos}: $node"
//        case None => s"consume $id"
//      }

    heuristicsSupporter.tryOperation[Heap, Term](description)(s, h, v)((s1, h1, v1, QS) => {
      consume(s1, h1, name, args, perms, locacc, pve, v1)((s2, h2, optSnap, v2) =>
        optSnap match {
          case Some(snap) =>
            QS(s2, h2, snap.convert(sorts.Snap), v2)
          case None =>
            /* Not having consumed anything could mean that we are in an infeasible
             * branch, or that the permission amount to consume was zero.
             * Returning a fresh snapshot in these cases should not lose any information.
             */
            val fresh = v2.decider.fresh(sorts.Snap)
            val s3 = s2.copy(functionRecorder = s2.functionRecorder.recordFreshSnapshot(fresh.applicable.asInstanceOf[Function]))
            QS(s3, h2, fresh, v2)
        })
    })(Q)
  }

  private def consume(s: State,
                      h: Heap,
                      name: String,
                      args: Seq[Term],
                      perms: Term,
                      locacc: ast.LocationAccess,
                      pve: PartialVerificationError,
                      v: Verifier)
                     (Q: (State, Heap, Option[Term], Verifier) => VerificationResult)
                     : VerificationResult = {

    /* [2016-05-27 Malte] Performing this check slows down the verification quite
     * a bit (from 4 minutes down to 5 minutes, for the whole test suite). Only
     * checking the property on-failure (within decider.withChunk) is likely to
     * perform better.
     */
//      if (decider.check(σ, perms === NoPerm(), config.checkTimeout())) {
//        /* Don't try looking for a chunk (which might fail) if zero permissions are
//         * to be consumed.
//         */
//        Q(h, None, c)
//      } else {
      if (s.exhaleExt) {
        /* TODO: Integrate magic wand's transferring consumption into the regular,
         * (non-)exact consumption (the code following this if-branch)
         */
        magicWandSupporter.transfer(s, name, args, perms, locacc, pve, v)((s1, optCh, v1) =>
          Q(s1, h, optCh.flatMap(ch => Some(ch.snap)), v1))
      } else if (Verifier.config.enableMoreCompleteExhale()) {
        consumeComplete(s, h, name, args, perms, locacc, pve, v)((s1, h1, snap1, v1) => {
          Q(s1, h1, snap1, v1)
        })
      } else {
        consumeGreedy(s, h, name, args, perms, locacc, pve, v)((s1, h1, snap1, v1) => {
          Q(s1, h1, snap1, v1)
        })
      }
//      }
  }

  private def consumeGreedy(s: State,
                    h: Heap,
                    name: String,
                    args: Seq[Term],
                    perms: Term,
                    locacc: ast.LocationAccess,
                    pve: PartialVerificationError,
                    v: Verifier)
                   (Q: (State, Heap, Option[Term], Verifier) => VerificationResult)
  : VerificationResult = {
    if (terms.utils.consumeExactRead(perms, s.constrainableARPs)) {
      withChunk(s, h, name, args, Some(perms), locacc, pve, v)((s1, h1, ch, v1) => {
        if (v1.decider.check(IsNonPositive(PermMinus(ch.perm, perms)), Verifier.config.checkTimeout()))
          Q(s1, h1 - ch, Some(ch.snap), v1)
        else
          Q(s1, h1 - ch + (ch - perms), Some(ch.snap), v1)
      })
    } else {
      withChunk(s, h, name, args, None, locacc, pve, v)((s1, h1, ch, v1) => {
        v1.decider.assume(PermLess(perms, ch.perm))
        Q(s1, h1 - ch + (ch - perms), Some(ch.snap), v1)
      })
    }
  }

  private def consumeComplete(s: State,
                   h: Heap,
                   name: String,
                   args: Seq[Term],
                   perms: Term,
                   locacc: ast.LocationAccess,
                   pve: PartialVerificationError,
                   v: Verifier)
                  (Q: (State, Heap, Option[Term], Verifier) => VerificationResult)
  : VerificationResult = {
    val relevantChunks = ListBuffer[BasicChunk]()
    val otherChunks = ListBuffer[Chunk]()
    h.values foreach {
      case c: BasicChunk if c.id.name == name => relevantChunks.append(c)
      case ch => otherChunks.append(ch)
    }

    if (relevantChunks.isEmpty) {
      // if no permission is exhaled, return fresh snapshot

      if (v.decider.check(perms === NoPerm(), Verifier.config.checkTimeout())) {
        Q(s, h, None, v)
      } else {
        Failure(pve dueTo InsufficientPermission(locacc)).withLoad(args)
      }
    } else {

      def setEqual(i1: Iterable[Term], i2: Iterable[Term]) = {
        if (i1.size != i2.size) {
          False()
        } else {
          And(i1.zip(i2).map { case (t1, t2) => Equals(t1, t2) })
        }
      }

      val consumeExact = terms.utils.consumeExactRead(perms, s.constrainableARPs)

      var pNeeded = perms
      var pSum: Term = NoPerm()
      val newChunks = ListBuffer[BasicChunk]()
      val equalities = ListBuffer[Term]()
      val sort = relevantChunks.head.snap.sort
      val fresh = v.decider.appliedFresh("basic_fresh", sort, s.relevantQuantifiedVariables)
      var moreNeeded = true

      // TODO: actual order heuristics
      relevantChunks.sortWith((b1, _) => b1.args == args) foreach { ch =>
        if (moreNeeded) {
          val eq = setEqual(ch.args, args)
          pSum = PermPlus(pSum, Ite(eq, ch.perm, NoPerm()))
          val pTakenBody = Ite(eq, PermMin(ch.perm, pNeeded), NoPerm())
          val pTakenMacro = v.decider.freshMacro("basic_pTaken", Seq(), pTakenBody)
          val pTaken = App(pTakenMacro, Seq())
          val newChunk = ch - pTaken
          equalities.append(Implies(And(IsPositive(ch.perm), eq), fresh === newChunk.snap))
          pNeeded = PermMinus(pNeeded, pTaken)

          if (!v.decider.check(IsNonPositive(newChunk.perm), Verifier.config.splitTimeout())) {
            newChunks.append(newChunk)
          }

          val toCheck = if (consumeExact) pNeeded === NoPerm() else IsPositive(pSum)
          moreNeeded = !v.decider.check(toCheck, Verifier.config.splitTimeout())
        } else {
          newChunks.append(ch)
        }
      }

      val allChunks = otherChunks ++ newChunks
      val interpreter = new PropertyInterpreter(allChunks, v)
      newChunks foreach { ch =>
        val resource = Resources.resourceDescriptions(ch.resourceID)
        v.decider.assume(interpreter.buildPathConditionsForChunk(ch, resource.instanceProperties))
        v.decider.assume(interpreter.buildPathConditionsForResource(ch.resourceID, resource.staticProperties))
      }
      v.decider.assume(equalities)

      val newHeap = Heap(allChunks)
      // TODO: remove cast
      val s1 = s.copy(functionRecorder = s.functionRecorder.recordFreshSnapshot(fresh.applicable.asInstanceOf[Function]))

      if (!moreNeeded) {
        if (!consumeExact) {
          v.decider.assume(PermLess(perms, pSum))
        }
        Q(s1, newHeap, Some(fresh), v)
      } else {
        val toCheck = if (consumeExact) pNeeded === NoPerm() else IsPositive(pSum)
        v.decider.assert(toCheck) {
          case true =>
            if (!consumeExact) {
              v.decider.assume(PermLess(perms, pSum))
            }
            Q(s1, newHeap, Some(fresh), v)
          case false => Failure(pve dueTo InsufficientPermission(locacc)).withLoad(args)
        }
      }
    }
  }

  /*
   * Looking up basic chunks
   */

  def withChunk(s: State,
                h: Heap,
                name: String,
                args: Seq[Term],
                locacc: ast.LocationAccess,
                pve: PartialVerificationError,
                v: Verifier)
               (Q: (State, Heap, BasicChunk, Verifier) => VerificationResult)
               : VerificationResult = {

    executionFlowController.tryOrFail2[Heap, BasicChunk](s.copy(h = h), v)((s1, v1, QS) =>
      unifiedHeapSupporter.findChunk[BasicChunk](s1.h.values, BasicChunkIdentifier(name), args, v1) match {
        case Some(chunk) =>
          QS(s1.copy(h = s.h), s1.h, chunk, v1)

        case None =>
          if (v1.decider.checkSmoke())
            Success() /* TODO: Mark branch as dead? */
          else
            Failure(pve dueTo InsufficientPermission(locacc)).withLoad(args)}
    )(Q)
  }

  def withChunk(s: State,
                h: Heap,
                name: String,
                args: Seq[Term],
                optPerms: Option[Term],
                locacc: ast.LocationAccess,
                pve: PartialVerificationError,
                v: Verifier)
               (Q: (State, Heap, BasicChunk, Verifier) => VerificationResult)
               : VerificationResult = {

    executionFlowController.tryOrFail2[Heap, BasicChunk](s.copy(h = h), v)((s1, v1, QS) =>
      withChunk(s1, s1.h, name, args, locacc, pve, v1)((s2, h2, ch, v2) => {
        val permCheck = optPerms match {
          case Some(p) => PermAtMost(p, ch.perm)
          case None => ch.perm !== NoPerm()
        }

        //        if (!isKnownToBeTrue(permCheck)) {
        //          val writer = bookkeeper.logfiles("withChunk")
        //          writer.println(permCheck)
        //        }

        v2.decider.assert(permCheck) {
          case true =>
            v2.decider.assume(permCheck)
            QS(s2.copy(h = s.h), h2, ch, v2)
          case false =>
            Failure(pve dueTo InsufficientPermission(locacc)).withLoad(args)
        }
      })
    )(Q)
  }

  def withChunk(s: State,
                name: String,
                args: Seq[Term],
                locacc: ast.LocationAccess,
                pve: PartialVerificationError,
                v: Verifier)
               (Q: (State, BasicChunk, Verifier) => VerificationResult)
               : VerificationResult =

    withChunk(s, s.h, name, args, locacc, pve, v)((s1, h1, ch, v1) =>
      Q(s1.copy(h = h1), ch, v1))

  def withChunk(s: State,
                name: String,
                args: Seq[Term],
                optPerms: Option[Term],
                locacc: ast.LocationAccess,
                pve: PartialVerificationError,
                v: Verifier)
               (Q: (State, BasicChunk, Verifier) => VerificationResult)
               : VerificationResult =

    withChunk(s, s.h, name, args, optPerms, locacc, pve, v)((s1, h1, ch, v1) =>
      Q(s1.copy(h = h1), ch, v1))

}