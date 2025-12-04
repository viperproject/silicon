// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.rules.chunks

import viper.silicon.interfaces.state._
import viper.silicon.interfaces.{Success, VerificationResult}
import viper.silicon.resources.{NonQuantifiedPropertyInterpreter, Resources}
import viper.silicon.rules._
import viper.silicon.state._
import viper.silicon.state.terms._
import viper.silicon.state.terms.perms.IsPositive
import viper.silicon.verifier.Verifier
import viper.silver.ast
import viper.silver.verifier.VerificationError

import scala.reflect.ClassTag

trait ChunkSupportRules extends SymbolicExecutionRules {
  def consume(s: State,
              h: Heap,
              resource: ast.Resource,
              args: Seq[Term],
              perms: Term,
              ve: VerificationError,
              v: Verifier,
              description: String)
             (Q: (State, Heap, Heap, Term, Verifier) => VerificationResult)
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
             (Q: (State, Heap, Heap, Term, Verifier) => VerificationResult)
             : VerificationResult = {

    consume2(s, h, resource, args, perms, ve, v)((s2, h2, hConsumed, optSnap, v2) =>
      optSnap match {
        case Some(snap) =>
          Q(s2, h2, hConsumed, snap.convert(sorts.Snap), v2)
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
          Q(s3, h2, hConsumed, fresh, v2)
      })
  }

  private def consume2(s: State,
                       h: Heap,
                       resource: ast.Resource,
                       args: Seq[Term],
                       perms: Term,
                       ve: VerificationError,
                       v: Verifier)
                      (Q: (State, Heap, Heap, Option[Term], Verifier) => VerificationResult)
                      : VerificationResult = {

    val id = ChunkIdentifier(resource, s.program)
    if (s.exhaleExt) {
      val failure = createFailure(ve, v, s)
      magicWandSupporter.transfer(s, perms, failure, Seq(), v)(moreCompleteExhaleSupporter.consumeSingleWithLoopStuff(resource, args, ve))((s1, optCh, v1) => {
              val cHeap = optCh match {
                case None => Heap()
                case Some(ch) => Heap(Seq(ch))
              } // ??? probably wrong
              Q(s1, h, cHeap, optCh.flatMap(ch => Some(ch match {
                case bc: BasicChunk => bc.snap
                case mwc: MagicWandChunk => mwc.snap
              })), v1)})
    } else {
      executionFlowController.tryOrFail2[(Heap, Heap), Option[Term]](s, v)((s1, v1, QS) =>
        // 2022-05-07 MHS: MoreCompleteExhale isn't yet integrated into function verification, hence the limitation to method verification
        if (s1.moreCompleteExhale) {
          moreCompleteExhaleSupporter.consumeComplete(s1, h, resource, args, perms, ve, v1, true)((s2, h2, hConsumed, snap2, v2) => {
            QS(s2, (h2, hConsumed), snap2, v2)
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
              QS(s2.copy(h = s.h), (h2, ???), snap, v1)
            case _ if v1.decider.checkSmoke(true) =>
              Success() // TODO: Mark branch as dead?
            case _ =>
              createFailure(ve, v1, s1, true)
          }
        }
      ){case (s3, (h3, cHeap3), snap3, v3) => Q(s3, h3, cHeap3, snap3, v3)}
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

    def assumeProperties(chunk: NonQuantifiedChunk, heap: Heap, s: State): Unit = {
      val interpreter = new NonQuantifiedPropertyInterpreter(heap.values, v, s)
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
            assumeProperties(newChunk, newHeap, s)
          }
          (ConsumptionResult(PermMinus(perms, toTake), Seq(), v, 0), s, newHeap, takenChunk)
        } else {
          if (v.decider.check(ch.perm !== NoPerm, Verifier.config.checkTimeout())) {
            v.decider.assume(PermLess(perms, ch.perm))
            val newChunk = ch.withPerm(PermMinus(ch.perm, perms))
            val takenChunk = ch.withPerm(perms)
            val newHeap = h - ch + newChunk
            assumeProperties(newChunk, newHeap, s)
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
    val (fr1, h1) = v.stateConsolidator(s).merge(s.functionRecorder, s, h, ch, v)
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

    executionFlowController.tryOrFail2[Heap, Term](s, v)((s1, v1, QS) => {
      {
        if (s1.loopPhaseStack.nonEmpty && (s1.loopPhaseStack.head._1 == LoopPhases.Transferring || s1.loopPhaseStack.head._1 == LoopPhases.Assuming)) {
          assert(s1.moreCompleteExhale)

          val identifier = resource match {
            case f: ast.Field => BasicChunkIdentifier(f.name)
            case p: ast.Predicate => BasicChunkIdentifier(p.name)
            case mw: ast.MagicWand => ??? // MagicWandIdentifier(mw, s.program)
          }
          val chs = chunkSupporter.findChunksWithID[NonQuantifiedChunk](h.values, identifier)
          val currentPermAmount =
            chs.foldLeft(NoPerm: Term)((q, ch) => {
              val argsPairWiseEqual = And(args.zip(ch.args).map { case (a1, a2) => a1 === a2 })
              PermPlus(q, Ite(argsPairWiseEqual, ch.perm, NoPerm))
            })
          val havePerm = IsPositive(currentPermAmount)
          joiner.join[(Heap, Term), (Heap, Term)](s1, v1, false)((s1p, v1p, QM) => {
            brancher.branch(s1p, havePerm, None, v1p)((s2, v2) => {
              moreCompleteExhaleSupporter.lookupComplete(s2, h, resource, args, ve, v2)((s3, tSnap, v3) =>
                QM(s3, (s3.h, tSnap), v3))
            },
              (s2, v2) => {
                val perms = s2.loopReadVarStack.head._1 // FractionPermLiteral(Rational(1, 100))

                def fn(s: State, h: Heap, resource: ast.Resource, args: Seq[Term], ve: VerificationError, v: Verifier)(QP: (State, Term, Verifier) => VerificationResult): VerificationResult = {
                  moreCompleteExhaleSupporter.consumeComplete(s, h, resource, args, perms, ve, v, true)((s2, h2, hConsumed, snap2, v2) => {
                    QP(s2, snap2.get, v2)
                  })
                }

                fn(s2, s2.h, resource, args, ve, v2)((s3, tSnap, v3) =>
                  QM(s3, (s3.h, tSnap), v3))
              })
          }) {
            case Seq(e) => (e.s, e.data)
            case Seq(e1, e2) =>
              val mergedState = State.merge(e1.s, e1.pathConditions, e2.s, e2.pathConditions)
              (mergedState, (mergedState.h, e1.data._2))
          }((s7, hs7, v7) => {
            QS(s7, hs7._1, hs7._2, v7)
          })
        } else {
          if (s1.moreCompleteExhale) {
            moreCompleteExhaleSupporter.lookupComplete(s1, s1.h, resource, args, ve, v1)((s2, tSnap, v2) =>
              QS(s2, s2.h, tSnap, v2))
          } else {
            lookupGreedy(s1, s1.h, resource, args, ve, v1)((s2, tSnap, v2) =>
              QS(s2, s2.h, tSnap, v2))
          }
        }
      }
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
    if (s.loopPhaseStack.nonEmpty)
      throw new Exception()

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
