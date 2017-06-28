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
import viper.silicon.state.terms.perms.IsNonPositive
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

  def produce(s: State, h: Heap, ch: BasicChunk, v: Verifier)
             (Q: (State, Heap, Verifier) => VerificationResult)
             : VerificationResult

  /* TODO: withChunk wraps getChunk in tryOrFail - is it worth exposing getChunk at all, i.e. is there an external use case for it? */

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
          QS(s2, h2, v2.decider.fresh(sorts.Snap), v2)
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
      } else {
        if (terms.utils.consumeExactRead(perms, s.constrainableARPs)) {
          withChunk(s, h, name, args, Some(perms), locacc, pve, v)((s1, h1, ch, v1) => {
            if (v1.decider.check(IsNonPositive(PermMinus(ch.perm, perms)), Verifier.config.checkTimeout()))
              Q(s1, h1 - ch, Some(ch.snap), v1)
            else
              Q(s1, h1 - ch + (ch - perms), Some(ch.snap), v1)})
        } else {
          withChunk(s, h, name, args, None, locacc, pve, v)((s1, h1, ch, v1) => {
            v1.decider.assume(PermLess(perms, ch.perm))
            Q(s1, h1 - ch + (ch - perms), Some(ch.snap), v1)})
        }
      }
//      }
  }

  private def consume2(s: State,
                       h: Heap,
                       name: String,
                       args: Seq[Term],
                       perms: Term,
                       locacc: ast.LocationAccess,
                       pve: PartialVerificationError,
                       v: Verifier)
                      (Q: (State, Heap, Option[Term], Verifier) => VerificationResult)
  : VerificationResult = {
    if (s.exhaleExt) {
      /* TODO: Integrate magic wand's transferring consumption into the regular,
       * (non-)exact consumption (the code following this if-branch)
       */
      magicWandSupporter.transfer(s, name, args, perms, locacc, pve, v)((s1, optCh, v1) =>
        Q(s1, h, optCh.flatMap(ch => Some(ch.snap)), v1))
    } else {
      if (terms.utils.consumeExactRead(perms, s.constrainableARPs)) {
        val relevantChunks = ListBuffer[BasicChunk]()
        val otherChunks = ListBuffer[Chunk]()
        s.h.values foreach {
          case c: BasicChunk if c.id.name == name => relevantChunks.append(c)
          case ch => otherChunks.append(ch)
        }
        if (relevantChunks.isEmpty) {
          Failure(pve dueTo InsufficientPermission(locacc)).withLoad(args)
        } else {
          var qNeeded = perms
          val newHeap = ListBuffer[BasicChunk]()
          val equalities = ListBuffer[Term]()
          val fresh = v.decider.fresh(relevantChunks.head.snap.sort)
          relevantChunks foreach { ch =>

            def setEqual(i1: Iterable[Term], i2: Iterable[Term]) = {
              if (i1.size != i2.size) {
                False()
              } else {
                And(i1.zip(i2).map { case (t1, t2) => Equals(t1, t2) })
              }
            }

            val eq = setEqual(ch.args, args)
            val qCurrent = Ite(eq, PermMin(ch.perm, qNeeded), NoPerm())
            val newChunk = ch - qCurrent
            equalities.append(Implies(And(PermLess(NoPerm(), ch.perm), eq), Equals(fresh, newChunk.snap)))
            qNeeded = PermMinus(qNeeded, qCurrent)
            newHeap.append(newChunk)
          }

          val interpreter = new PropertyInterpreter(v, newHeap)
          newHeap foreach { ch =>
            val resource = Resources.resourceDescriptions(ch.resourceID)
            v.decider.assume(interpreter.buildPathConditionsForChunk(ch, resource.instanceProperties))
            v.decider.assume(interpreter.buildPathConditionsForResource(ch.resourceID, resource.staticProperties))
          }
          v.decider.assume(equalities)

          v.decider.assert(Equals(qNeeded, NoPerm())) {
            case true => Q(s, Heap(otherChunks ++ newHeap), Some(fresh), v)
            case false => Failure(pve dueTo InsufficientPermission(locacc)).withLoad(args)
          }
        }
      } else {
        withChunk(s, h, name, args, None, locacc, pve, v)((s1, h1, ch, v1) => {
          v1.decider.assume(PermLess(perms, ch.perm))
          Q(s1, h1 - ch + (ch - perms), Some(ch.snap), v1)})
      }
    }
  }

  def produce(s: State, h: Heap, ch: BasicChunk, v: Verifier)
             (Q: (State, Heap, Verifier) => VerificationResult)
             : VerificationResult = {

    val (h1, _) = stateConsolidator.merge(h, ch, v)

    Q(s, h1, v)
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

private case class PermissionsConsumptionResult(consumedCompletely: Boolean)
