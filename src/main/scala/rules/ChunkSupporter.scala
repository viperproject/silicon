// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.rules

import scala.reflect.ClassTag
import viper.silver.ast
import viper.silver.verifier.VerificationError
import viper.silicon.interfaces.state._
import viper.silicon.interfaces.{Success, VerificationResult}
import viper.silicon.resources.{NonQuantifiedPropertyInterpreter, Resources}
import viper.silicon.state._
import viper.silicon.state.terms._
import viper.silicon.state.terms.perms.IsPositive
import viper.silicon.verifier.Verifier

trait ChunkSupportRules extends SymbolicExecutionRules {
  def consume(s: State,
              h: Heap,
              resource: ast.Resource,
              args: Seq[Term],
              perms: Term,
              ve: VerificationError,
              v: Verifier,
              description: String)
             (Q: (State, Heap, Term, Verifier) => VerificationResult)
             : VerificationResult

  def produce(s: State, h: Heap, ch: NonQuantifiedChunk, v: Verifier)
             (Q: (State, Heap, Verifier) => VerificationResult)
             : VerificationResult

  def lookup(s: State,
             h: Heap,
             resource: ast.Resource,
             args: Seq[Term],
             ve: VerificationError,
             v: Verifier)
            (Q: (State, Heap, Term, Verifier) => VerificationResult)
            : VerificationResult

  def findChunk[CH <: NonQuantifiedChunk: ClassTag]
               (chunks: Iterable[Chunk],
                id: ChunkIdentifer,
                args: Iterable[Term],
                v: Verifier)
               : Option[CH]

  def findMatchingChunk[CH <: NonQuantifiedChunk: ClassTag]
                       (chunks: Iterable[Chunk],
                        chunk: CH,
                        v: Verifier)
                       : Option[CH]

  def findChunksWithID[CH <: NonQuantifiedChunk: ClassTag]
                      (chunks: Iterable[Chunk],
                       id: ChunkIdentifer)
                      : Iterable[CH]
}

object chunkSupporter extends ChunkSupportRules {
  def consume(s: State,
              h: Heap,
              resource: ast.Resource,
              args: Seq[Term],
              perms: Term,
              ve: VerificationError,
              v: Verifier,
              description: String)
             (Q: (State, Heap, Term, Verifier) => VerificationResult)
             : VerificationResult = {

    consume2(s, h, resource, args, perms, ve, v)((s2, h2, optSnap, v2) =>
      optSnap match {
        case Some(snap) =>
          Q(s2, h2, snap.convert(sorts.Snap), v2)
        case None =>
          /* Not having consumed anything could mean that we are in an infeasible
           * branch, or that the permission amount to consume was zero.
           *
           * [MS 2022-01-28] Previously, a a fresh snapshot was retured, which also had to be
           * registered with the function recorder. However, since nothing was consumed,
           * returning the unit snapshot seems more appropriate.
           */
          val fresh = v2.decider.fresh(sorts.Snap)
          val s3 = s2.copy(functionRecorder = s2.functionRecorder.recordFreshSnapshot(fresh.applicable))
          Q(s3, h2, fresh, v2)
      })
  }

  private def consume2(s: State,
                       h: Heap,
                       resource: ast.Resource,
                       args: Seq[Term],
                       perms: Term,
                       ve: VerificationError,
                       v: Verifier)
                      (Q: (State, Heap, Option[Term], Verifier) => VerificationResult)
                      : VerificationResult = {

    val id = ChunkIdentifier(resource, s.program)
    if (s.exhaleExt) {
      val failure = createFailure(ve, v, s)
      magicWandSupporter.transfer(s, perms, failure, Seq(), v)(consumeGreedy(_, _, id, args, _, _))((s1, optCh, v1) =>
        Q(s1, h, optCh.flatMap(ch => Some(ch.snap)), v1))
    } else {
      executionFlowController.tryOrFail2[Heap, Option[Term]](s.copy(h = h), v)((s1, v1, QS) =>
        if (s1.moreCompleteExhale) {
          moreCompleteExhaleSupporter.consumeComplete(s1, s1.h, resource, args, perms, ve, v1)((s2, h2, snap2, v2) => {
            QS(s2.copy(h = s.h), h2, snap2, v2)
          })
        } else {
          consumeGreedy(s1, s1.h, id, args, perms, v1) match {
            case (Complete(), s2, h2, optCh2) =>
              val snap = optCh2 match {
                case None => None
                case Some(ch) =>
                  if (v1.decider.check(IsPositive(perms), Verifier.config.checkTimeout())) {
                    Some(ch.snap)
                  } else {
                    Some(Ite(IsPositive(perms), ch.snap.convert(sorts.Snap), Unit))
                  }
              }
              QS(s2.copy(h = s.h), h2, snap, v1)
            case _ if v1.decider.checkSmoke(true) =>
              Success() // TODO: Mark branch as dead?
            case _ =>
              createFailure(ve, v1, s1, true)
          }
        }
      )(Q)
    }
  }

  private def consumeGreedy(s: State,
                            h: Heap,
                            id: ChunkIdentifer,
                            args: Seq[Term],
                            perms: Term,
                            v: Verifier)
                           : (ConsumptionResult, State, Heap, Option[NonQuantifiedChunk]) = {

    val consumeExact = terms.utils.consumeExactRead(perms, s.constrainableARPs)

    def assumeProperties(chunk: NonQuantifiedChunk, heap: Heap): Unit = {
      val interpreter = new NonQuantifiedPropertyInterpreter(heap.values, v)
      val resource = Resources.resourceDescriptions(chunk.resourceID)
      v.decider.assume(interpreter.buildPathConditionsForChunk(chunk, resource.instanceProperties))
    }

    findChunk[NonQuantifiedChunk](h.values, id, args, v) match {
      case Some(ch) =>
        if (consumeExact) {
          val toTake = PermMin(ch.perm, perms)
          val newChunk = ch.withPerm(PermMinus(ch.perm, toTake))
          val takenChunk = Some(ch.withPerm(toTake))
          var newHeap = h - ch
          if (!v.decider.check(newChunk.perm === NoPerm, Verifier.config.checkTimeout())) {
            newHeap = newHeap + newChunk
            assumeProperties(newChunk, newHeap)
          }
          (ConsumptionResult(PermMinus(perms, toTake), Seq(), v, 0), s, newHeap, takenChunk)
        } else {
          if (v.decider.check(ch.perm !== NoPerm, Verifier.config.checkTimeout())) {
            v.decider.assume(PermLess(perms, ch.perm))
            val newChunk = ch.withPerm(PermMinus(ch.perm, perms))
            val takenChunk = ch.withPerm(perms)
            val newHeap = h - ch + newChunk
            assumeProperties(newChunk, newHeap)
            (Complete(), s, newHeap, Some(takenChunk))
          } else {
            (Incomplete(perms), s, h, None)
          }
        }
      case None =>
        if (consumeExact && s.retrying && v.decider.check(perms === NoPerm, Verifier.config.checkTimeout())) {
          (Complete(), s, h, None)
        } else {
          (Incomplete(perms), s, h, None)
        }
    }
  }

  def produce(s: State, h: Heap, ch: NonQuantifiedChunk, v: Verifier)
             (Q: (State, Heap, Verifier) => VerificationResult)
             : VerificationResult = {

    // Try to merge the chunk into the heap by finding an alias.
    // In any case, property assumptions are added after the merge step.
    val (fr1, h1) = v.stateConsolidator(s).merge(s.functionRecorder, h, ch, v)
    Q(s.copy(functionRecorder = fr1), h1, v)
  }

  def lookup(s: State,
             h: Heap,
             resource: ast.Resource,
             args: Seq[Term],
             ve: VerificationError,
             v: Verifier)
            (Q: (State, Heap, Term, Verifier) => VerificationResult)
            : VerificationResult = {

    executionFlowController.tryOrFail2[Heap, Term](s.copy(h = h), v)((s1, v1, QS) => {
      val lookupFunction =
        if (s1.moreCompleteExhale) moreCompleteExhaleSupporter.lookupComplete _
        else lookupGreedy _
      lookupFunction(s1, s1.h, resource, args, ve, v1)((s2, tSnap, v2) =>
        QS(s2.copy(h = s.h), s2.h, tSnap, v2))
    })(Q)
  }

  private def lookupGreedy(s: State,
                           h: Heap,
                           resource: ast.Resource,
                           args: Seq[Term],
                           ve: VerificationError,
                           v: Verifier)
                          (Q: (State, Term, Verifier) => VerificationResult)
                          : VerificationResult = {

    val id = ChunkIdentifier(resource, s.program)
    val findRes = findChunk[NonQuantifiedChunk](h.values, id, args, v)
    findRes match {
      case Some(ch) if v.decider.check(IsPositive(ch.perm), Verifier.config.checkTimeout()) =>
        Q(s, ch.snap, v)
      case _ if v.decider.checkSmoke(true) =>
        Success() // TODO: Mark branch as dead?
      case _ =>
        createFailure(ve, v, s, true)
    }
  }

  def findChunk[CH <: NonQuantifiedChunk: ClassTag]
               (chunks: Iterable[Chunk],
                id: ChunkIdentifer,
                args: Iterable[Term],
                v: Verifier)
               : Option[CH] = {
    val relevantChunks = findChunksWithID[CH](chunks, id)
    findChunkLiterally(relevantChunks, args) orElse findChunkWithProver(relevantChunks, args, v)
  }

  def findMatchingChunk[CH <: NonQuantifiedChunk: ClassTag]
                       (chunks: Iterable[Chunk], chunk: CH, v: Verifier): Option[CH] = {
    findChunk[CH](chunks, chunk.id, chunk.args, v)
  }

  def findChunksWithID[CH <: NonQuantifiedChunk: ClassTag](chunks: Iterable[Chunk], id: ChunkIdentifer): Iterable[CH] = {
    chunks.flatMap {
      case c: CH if id == c.id => Some(c)
      case _ => None
    }
  }

/** Extract the chunks with resource matching id.
 * Return two sequences of chunks -- one with resource id, and the
 * other with the remaining resources.
 */
  def splitHeap[CH <: NonQuantifiedChunk : ClassTag](h: Heap, id: ChunkIdentifer)
                                                   : (Seq[CH], Seq[Chunk]) = {

    var relevantChunks = Seq[CH]()
    var otherChunks = Seq[Chunk]()

    h.values foreach {
      case ch: CH if ch.id == id =>
        relevantChunks +:= ch
      case ch: QuantifiedChunk if ch.id == id =>
        sys.error(
          s"I did not expect quantified chunks on the heap for resource $id, "
            + s"but found $ch")
      case ch =>
        otherChunks +:= ch
    }

    (relevantChunks, otherChunks)
  }
  private def findChunkLiterally[CH <: NonQuantifiedChunk](chunks: Iterable[CH], args: Iterable[Term]) = {
    chunks find (ch => ch.args == args)
  }

  private def findChunkWithProver[CH <: NonQuantifiedChunk](chunks: Iterable[CH], args: Iterable[Term], v: Verifier) = {
    chunks find (ch =>
      args.size == ch.args.size &&
      v.decider.check(And(ch.args zip args map (x => x._1 === x._2)), Verifier.config.checkTimeout()))
  }
}
