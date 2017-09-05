/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.rules

import scala.collection.mutable.ListBuffer
import scala.reflect.ClassTag
import viper.silver.verifier.VerificationError
import viper.silicon.interfaces.state._
import viper.silicon.interfaces.{Failure, Success, VerificationResult}
import viper.silicon.resources.{NonQuantifiedPropertyInterpreter, Resources}
import viper.silicon.state._
import viper.silicon.state.terms._
import viper.silicon.state.terms.perms.{IsNonPositive, IsPositive}
import viper.silicon.verifier.Verifier

trait ChunkSupportRules extends SymbolicExecutionRules {
  def consume(s: State,
              h: Heap,
              id: ChunkIdentifer,
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
             id: ChunkIdentifer,
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

object chunkSupporter extends ChunkSupportRules with Immutable {
  def consume(s: State,
              h: Heap,
              id: ChunkIdentifer,
              args: Seq[Term],
              perms: Term,
              ve: VerificationError,
              v: Verifier,
              description: String)
             (Q: (State, Heap, Term, Verifier) => VerificationResult)
             : VerificationResult = {
    heuristicsSupporter.tryOperation[Heap, Term](description)(s, h, v)((s1, h1, v1, QS) => {
      consume(s1, h1, id, args, perms, ve, v1)((s2, h2, optSnap, v2) =>
        optSnap match {
          case Some(snap) =>
            QS(s2, h2, snap.convert(sorts.Snap), v2)
          case None =>
            /* Not having consumed anything could mean that we are in an infeasible
             * branch, or that the permission amount to consume was zero.
             * Returning a fresh snapshot in these cases should not lose any information.
             */
            val fresh = v2.decider.fresh(sorts.Snap)
            val s3 = s2.copy(functionRecorder = s2.functionRecorder.recordFreshSnapshot(fresh.applicable))
            QS(s3, h2, fresh, v2)
        })
    })(Q)
  }

  private def consume(s: State,
                      h: Heap,
                      id: ChunkIdentifer,
                      args: Seq[Term],
                      perms: Term,
                      ve: VerificationError,
                      v: Verifier)
                     (Q: (State, Heap, Option[Term], Verifier) => VerificationResult)
                     : VerificationResult = {
    if (s.exhaleExt) {
      val failure = Failure(ve).withLoad(args)
      magicWandSupporter.transfer(s, perms, failure, v)(consumeGreedy(_, _, id, args, _, _))((s1, optCh, v1) =>
        Q(s1, h, optCh.flatMap(ch => Some(ch.snap)), v1))
    } else {
      executionFlowController.tryOrFail2[Heap, Option[Term]](s.copy(h = h), v)((s1, v1, QS) =>
        if (Verifier.config.enableMoreCompleteExhale()) {
          consumeComplete(s1, s1.h, id, args, perms, ve, v1)((s2, h2, snap2, v2) => {
            QS(s2.copy(h = s.h), h2, snap2, v2)
          })
        } else {
          consumeGreedy(s1, s1.h, id, args, perms, v1) match {
            case (Complete(), s2, h2, optCh2) =>
              QS(s2.copy(h = s.h), h2, optCh2.map(_.snap), v1)
            case _ if v1.decider.checkSmoke() =>
              Success() // TODO: Mark branch as dead?
            case _ =>
              Failure(ve).withLoad(args)
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
                            v: Verifier) = {
    val consumeExact = terms.utils.consumeExactRead(perms, s.constrainableARPs)

    def assumeProperties(chunk: NonQuantifiedChunk, heap: Heap) = {
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
          if (v.decider.check(newChunk.perm === NoPerm(), Verifier.config.checkTimeout())) {
            (ConsumptionResult(PermMinus(perms, toTake), v), s, h - ch, takenChunk)
          } else {
            val newHeap = h - ch + newChunk
            assumeProperties(newChunk, newHeap)
            (ConsumptionResult(PermMinus(perms, toTake), v), s, newHeap, takenChunk)
          }
        } else {
          if (v.decider.check(ch.perm !== NoPerm(), Verifier.config.checkTimeout())) {
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
        if (consumeExact && s.retrying && v.decider.check(perms === NoPerm(), Verifier.config.checkTimeout())) {
          (Complete(), s, h, None)
        } else {
          (Incomplete(perms), s, h, None)
        }
    }
  }

  private def consumeComplete(s: State,
                              h: Heap,
                              id: ChunkIdentifer,
                              args: Seq[Term],
                              perms: Term,
                              ve: VerificationError,
                              v: Verifier)
                             (Q: (State, Heap, Option[Term], Verifier) => VerificationResult)
                             : VerificationResult = {
    val relevantChunks = ListBuffer[NonQuantifiedChunk]()
    val otherChunks = ListBuffer[Chunk]()
    h.values foreach {
      case c: NonQuantifiedChunk if id == c.id => relevantChunks.append(c)
      case ch => otherChunks.append(ch)
    }

    if (relevantChunks.isEmpty) {
      // if no permission is exhaled, return none
      if (v.decider.check(perms === NoPerm(), Verifier.config.checkTimeout())) {
        Q(s, h, None, v)
      } else {
        Failure(ve).withLoad(args)
      }
    } else {
      val consumeExact = terms.utils.consumeExactRead(perms, s.constrainableARPs)

      var pNeeded = perms
      var pSum: Term = NoPerm()
      val newChunks = ListBuffer[NonQuantifiedChunk]()
      val constraints = ListBuffer[(Term, Term)]()
      var moreNeeded = true

      val definiteAlias = findChunk[NonQuantifiedChunk](relevantChunks, id, args, v)

      val sortFunction: (NonQuantifiedChunk, NonQuantifiedChunk) => Boolean = (ch1, ch2) => {
        // The definitive alias and syntactic aliases should get priority, since it is always
        // possible to consume from them
        definiteAlias.contains(ch1) || !definiteAlias.contains(ch2) && ch1.args == args
      }

      relevantChunks.sortWith(sortFunction) foreach { ch =>
        if (moreNeeded) {
          val eq = And(ch.args.zip(args).map { case (t1, t2) => t1 === t2 })
          pSum = PermPlus(pSum, Ite(eq, ch.perm, NoPerm()))
          val pTakenBody = Ite(eq, PermMin(ch.perm, pNeeded), NoPerm())
          val pTakenMacro = v.decider.freshMacro("complete_pTaken", Seq(), pTakenBody)
          val pTaken = App(pTakenMacro, Seq())
          val newChunk = ch.withPerm(PermMinus(ch.perm, pTaken))
          constraints.append((And(eq, IsPositive(ch.perm)), newChunk.snap))
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

      // A fresh snapshot is only needed, if we are consuming no permissions and
      // there is no definite alias with a non-zero permission amount
      val toCheck = Or(IsPositive(perms), IsPositive(definiteAlias.map(_.perm).getOrElse(NoPerm())))
      val s1 = if (consumeExact && !v.decider.check(toCheck, Verifier.config.checkTimeout())) {
        val sort = relevantChunks.head.snap.sort
        val fresh = v.decider.fresh(sort)
        constraints.append((True(), fresh))
        s.copy(functionRecorder = s.functionRecorder.recordFreshSnapshot(fresh.applicable))
      } else {
        s
      }

      // Creates the snapshot that is returned by the consume method
      // by building a conditional expression
      def createSnapshot(constraints: List[(Term, Term)]): Option[Term] = constraints match {
        case (_, sn) :: Nil => Some(sn)
        case (eq, sn) :: tail => createSnapshot(tail).flatMap(s => Some(Ite(eq, sn, s)))
        case _ => None
      }

      val snap = createSnapshot(constraints.toList)

      val allChunks = otherChunks ++ newChunks
      val interpreter = new NonQuantifiedPropertyInterpreter(allChunks, v)
      newChunks foreach { ch =>
        val resource = Resources.resourceDescriptions(ch.resourceID)
        v.decider.assume(interpreter.buildPathConditionsForChunk(ch, resource.instanceProperties))
      }

      val newHeap = Heap(allChunks)

      if (!moreNeeded) {
        if (!consumeExact) {
          v.decider.assume(PermLess(perms, pSum))
        }
        Q(s1, newHeap, snap, v)
      } else {
        val toAssert = if (consumeExact) pNeeded === NoPerm() else IsPositive(pSum)
        v.decider.assert(toAssert) {
          case true =>
            if (!consumeExact) {
              v.decider.assume(PermLess(perms, pSum))
            }
            Q(s1, newHeap, snap, v)
          case false =>
            Failure(ve).withLoad(args)
        }
      }
    }
  }

  def produce(s: State, h: Heap, ch: NonQuantifiedChunk, v: Verifier)
             (Q: (State, Heap, Verifier) => VerificationResult) = {
    // Try to merge the chunk into the heap by finding an alias.
    // In any case, property assumptions are added after the merge step.
    Q(s, stateConsolidator.merge(h, ch, v), v)
  }

  def lookup(s: State,
             h: Heap,
             id: ChunkIdentifer,
             args: Seq[Term],
             ve: VerificationError,
             v: Verifier)
            (Q: (State, Heap, Term, Verifier) => VerificationResult)
            : VerificationResult = {
    executionFlowController.tryOrFail2[Heap, Term](s.copy(h = h), v)((s1, v1, QS) => {
      val lookupFunction = if (Verifier.config.enableMoreCompleteExhale()) lookupComplete _ else lookupGreedy _
      lookupFunction(s1, s1.h, id, args, ve, v1)((s2, tSnap, v2) => {
          QS(s2.copy(h = s.h), s2.h, tSnap, v2)
      })
    })(Q)
  }

  private def lookupGreedy(s: State,
                           h: Heap,
                           id: ChunkIdentifer,
                           args: Seq[Term],
                           ve: VerificationError,
                           v: Verifier)
                          (Q: (State, Term, Verifier) => VerificationResult)
                          : VerificationResult = {
    findChunk[NonQuantifiedChunk](h.values, id, args, v) match {
      case Some(ch) if v.decider.check(IsPositive(ch.perm), Verifier.config.checkTimeout()) =>
        Q(s, ch.snap, v)
      case _ if v.decider.checkSmoke() =>
        Success() // TODO: Mark branch as dead?
      case _ =>
        Failure(ve).withLoad(args)
    }
  }

  private def lookupComplete(s: State,
                             h: Heap,
                             id: ChunkIdentifer,
                             args: Seq[Term],
                             ve: VerificationError,
                             v: Verifier)
                            (Q: (State, Term, Verifier) => VerificationResult)
                            : VerificationResult = {
    val relevantChunks = findChunksWithID[NonQuantifiedChunk](h.values, id).toSeq

    if (relevantChunks.isEmpty) {
      if (v.decider.checkSmoke()) {
        Success() // TODO: Mark branch as dead?
      } else {
        Failure(ve).withLoad(args)
      }
    } else {
      var pSum: Term = NoPerm()
      val constraints = ListBuffer[(Term, Term)]()
      var moreNeeded = true

      val definiteAlias = findChunk[NonQuantifiedChunk](relevantChunks, id, args, v)

      val sortFunction: (NonQuantifiedChunk, NonQuantifiedChunk) => Boolean = (ch1, ch2) => {
        // The definitive alias should get priority, since it is always possible to consume from it
        // Else, look for a syntactic alias
        definiteAlias.contains(ch1) || !definiteAlias.contains(ch2) && ch1.args == args
      }

      relevantChunks.sortWith(sortFunction) foreach { ch =>
        if (moreNeeded) {
          val eq = And(ch.args.zip(args).map { case (t1, t2) => t1 === t2 })
          pSum = PermPlus(pSum, Ite(eq, ch.perm, NoPerm()))
          constraints.append((And(eq, IsPositive(ch.perm)), ch.snap))
          moreNeeded = !v.decider.check(IsPositive(pSum), Verifier.config.splitTimeout())
        }
      }

      // Creates the snapshot that is returned by the lookup method
      // by building a conditional expression
      def createSnapshot(constraints: List[(Term, Term)]): Term = constraints match {
        case (_, sn) :: Nil => sn
        case (eq, sn) :: tail => Ite(eq, sn, createSnapshot(tail))
        case _ => sys.error("Should never happen, since relevant chunks is non-empty")
      }

      val snap = createSnapshot(constraints.toList)

      if (!moreNeeded) {
        Q(s, snap, v)
      } else {
        v.decider.assert(IsPositive(pSum)) {
          case true =>
            Q(s, snap, v)
          case false =>
            Failure(ve).withLoad(args)
        }
      }
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

  private def findChunkLiterally[CH <: NonQuantifiedChunk](chunks: Iterable[CH], args: Iterable[Term]) = {
    chunks find (ch => ch.args == args)
  }

  private def findChunkWithProver[CH <: NonQuantifiedChunk](chunks: Iterable[CH], args: Iterable[Term], v: Verifier) = {
    chunks find (ch =>
      args.size == ch.args.size &&
      v.decider.check(And(ch.args zip args map (x => x._1 === x._2)), Verifier.config.checkTimeout()))
  }
}
