// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.rules

import scala.collection.mutable.ListBuffer
import viper.silicon.{MList, MMap}
import viper.silicon.interfaces.state._
import viper.silicon.interfaces.{Failure, Success, VerificationResult}
import viper.silicon.logger.SymbExLogger
import viper.silicon.resources.{FieldID, NonQuantifiedPropertyInterpreter, Resources}
import viper.silicon.rules.chunkSupporter.findChunksWithID
import viper.silicon.state._
import viper.silicon.state.terms._
import viper.silicon.state.terms.perms.{IsNonPositive, IsPositive}
import viper.silicon.supporters.functions.NoopFunctionRecorder
import viper.silicon.verifier.Verifier
import viper.silver.ast
import viper.silver.verifier.VerificationError

object moreCompleteExhaleSupporter extends Immutable {
  sealed trait TaggedSummarisingSnapshot {
    def snapshot: Term
  }

  final case class FreshSummarisingSnapshot(snapshot: Term) extends TaggedSummarisingSnapshot
  final case class ReusedSummarisingSnapshot(snapshot: Term) extends TaggedSummarisingSnapshot

  private def summariseOnly(s: State,
                            relevantChunks: Seq[NonQuantifiedChunk],
                            resource: ast.Resource,
                            args: Seq[Term],
                            v: Verifier)
                           : (State, TaggedSummarisingSnapshot, Seq[Term], Term) = {

    // TODO: Since relevantChunks is a sequence, the order of the chunks affects caching, but shouldn't.
    //       An order-agnostic way of caching, would be better. A simple benchmark should reveal how
    //       many cache misses are due to order changes.

    // TODO: Caching would be more effective if the summary were created independently of the provided
    //       args. E.g. the summary could be created with free arguments ?a1, ?a2, ...; this summary
    //       could be cached, and ?a1 etc. would be replaced before returning the summary to the caller.

    s.ssCache.get((resource, relevantChunks, args)) match {
      case Some((_taggedSummarisingSnapshot, _summarisingSnapshotDefinitions, _permissionSum)) =>
        return (s, _taggedSummarisingSnapshot, _summarisingSnapshotDefinitions, _permissionSum)
      case _ =>
        /* Cache miss */
    }

    val sort: Sort =
      resource match {
        case f: ast.Field => v.symbolConverter.toSort(f.typ)
        case _: ast.Predicate => sorts.Snap
        case _: ast.MagicWand => sorts.Snap
      }

    val `?s` = Var(Identifier("?s"), sort)
    var summarisingSnapshotDefinitions: Seq[Term] = Vector.empty
    var permissionSum: Term = NoPerm()

    relevantChunks.foreach(ch => {
      val argumentEqualities =
        And(ch.args.zip(args).map { case (t1, t2) => t1 === t2 })

      summarisingSnapshotDefinitions :+=
        Implies(And(argumentEqualities, IsPositive(ch.perm)), `?s` === ch.snap)

      permissionSum =
        PermPlus(permissionSum, Ite(argumentEqualities, ch.perm, NoPerm()))
    })

    val taggedSummarisingSnapshot =
      summarisingSnapshotDefinitions
        .collectFirst {
          case Equals(`?s`, snap) => ReusedSummarisingSnapshot(snap)
        }.getOrElse({
          // val ss = v.decider.appliedFresh("ss", sort, s.relevantQuantifiedVariables)
          val ss = v.decider.appliedFresh("ss", sort, s.functionRecorderQuantifiedVariables())
          FreshSummarisingSnapshot(ss)
        })

    val summarisingSnapshot = taggedSummarisingSnapshot.snapshot

    summarisingSnapshotDefinitions =
      summarisingSnapshotDefinitions map (_.replace(`?s`, summarisingSnapshot))

    val ssc1 = s.ssCache + ((resource, relevantChunks, args) -> (taggedSummarisingSnapshot, summarisingSnapshotDefinitions, permissionSum))
    val s1 = s.copy(ssCache = ssc1)

    (s1, taggedSummarisingSnapshot, summarisingSnapshotDefinitions, permissionSum)
  }

  private def summarise(s: State,
                        relevantChunks: Seq[NonQuantifiedChunk],
                        resource: ast.Resource,
                        args: Seq[Term],
                        v: Verifier)
                       (Q: (State, Term, Seq[Term], Term, Verifier) => VerificationResult)
                       : VerificationResult = {

    if (relevantChunks.size == 1) {
      val chunk = relevantChunks.head
      if (v.decider.check(And(chunk.args.zip(args).map { case (t1, t2) => t1 === t2 }), Verifier.config.checkTimeout())) {
        return Q(s, chunk.snap, Seq(), chunk.perm, v)
      } else {
        return Q(s, chunk.snap, Seq(), NoPerm(), v)
      }
    }
    val (s1, taggedSnap, snapDefs, permSum) = summariseOnly(s, relevantChunks, resource, args, v)

    v.decider.assume(And(snapDefs))
//    v.decider.assume(PermAtMost(permSum, FullPerm())) /* Done in StateConsolidator instead */

    val s2 =
      taggedSnap match {
        case _: FreshSummarisingSnapshot =>
          val smd = SnapshotMapDefinition(resource, taggedSnap.snapshot, snapDefs, Seq.empty)
          val fr2 = s1.functionRecorder.recordFvfAndDomain(smd)

          s1.copy(functionRecorder = fr2)
        case _ =>
          s1
      }

    Q(s2, taggedSnap.snapshot, snapDefs, permSum, v)
  }

  def lookupComplete(s: State,
                     h: Heap,
                     resource: ast.Resource,
                     args: Seq[Term],
                     ve: VerificationError,
                     v: Verifier)
                    (Q: (State, Term, Verifier) => VerificationResult)
                    : VerificationResult = {

    val id = ChunkIdentifier(resource, Verifier.program)
    val relevantChunks = findChunksWithID[NonQuantifiedChunk](h.values, id).toSeq

    if (relevantChunks.isEmpty) {
      if (v.decider.checkSmoke()) {
        Success() // TODO: Mark branch as dead?
      } else {
        Failure(ve).withLoad(args)
      }
    } else {
      summarise(s, relevantChunks, resource, args, v)((s1, snap, _, permSum, v1) =>
        v.decider.assert(IsPositive(permSum)) {
          case true =>
            Q(s1, snap, v1)
          case false =>
            Failure(ve).withLoad(args)
        })
    }
  }

  def consumeComplete(s: State,
                      h: Heap,
                      resource: ast.Resource,
                      args: Seq[Term],
                      perms: Term,
                      ve: VerificationError,
                      v: Verifier)
                     (Q: (State, Heap, Option[Term], Verifier) => VerificationResult)
                     : VerificationResult = {

    if (s.functionRecorder == NoopFunctionRecorder && !s.hackIssue387DisablePermissionConsumption)
      actualConsumeComplete(s, h, resource, args, perms, ve, v)(Q)
    else
      summariseHeapAndAssertReadAccess(s, h, resource, args, perms, ve, v)(Q)
  }

  private def summariseHeapAndAssertReadAccess(s: State,
                                               h: Heap,
                                               resource: ast.Resource,
                                               args: Seq[Term],
                                               perms: Term,
                                               ve: VerificationError,
                                               v: Verifier)
                                              (Q: (State, Heap, Option[Term], Verifier) => VerificationResult)
                                              : VerificationResult = {

    val id = ChunkIdentifier(resource, Verifier.program)
    val relevantChunks = findChunksWithID[NonQuantifiedChunk](h.values, id).toSeq

    summarise(s, relevantChunks, resource, args, v)((s1, snap, _, permSum, v1) =>
      v.decider.assert(IsPositive(permSum)) {
        case true =>
          Q(s1, h, Some(snap), v1)
        case false =>
          Failure(ve).withLoad(args)
      })
  }

  private def actualConsumeComplete(s: State,
                                    h: Heap,
                                    resource: ast.Resource,
                                    args: Seq[Term],
                                    perms: Term,
                                    ve: VerificationError,
                                    v: Verifier)
                                   (Q: (State, Heap, Option[Term], Verifier) => VerificationResult)
                                   : VerificationResult = {

    val id = ChunkIdentifier(resource, Verifier.program)
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
      var moreNeeded = true

      val definiteAlias = chunkSupporter.findChunk[NonQuantifiedChunk](relevantChunks, id, args, v)

      val sortFunction: (NonQuantifiedChunk, NonQuantifiedChunk) => Boolean = (ch1, ch2) => {
        // The definitive alias and syntactic aliases should get priority, since it is always
        // possible to consume from them
        definiteAlias.contains(ch1) || !definiteAlias.contains(ch2) && ch1.args == args
      }

      val additionalArgs = s.relevantQuantifiedVariables
      var currentFunctionRecorder = s.functionRecorder

      relevantChunks.sortWith(sortFunction) foreach { ch =>
        if (moreNeeded) {
          val eq = And(ch.args.zip(args).map { case (t1, t2) => t1 === t2 })
          pSum = PermPlus(pSum, Ite(eq, ch.perm, NoPerm()))
          val pTakenBody = Ite(eq, PermMin(ch.perm, pNeeded), NoPerm())
          val pTakenArgs = additionalArgs
          val pTakenDecl = v.decider.freshMacro("mce_pTaken", pTakenArgs, pTakenBody)
          val pTakenMacro = Macro(pTakenDecl.id, pTakenDecl.args.map(_.sort), pTakenDecl.body.sort)
          val pTaken = App(pTakenMacro, pTakenArgs)

          currentFunctionRecorder = currentFunctionRecorder.recordFreshMacro(pTakenDecl)
          SymbExLogger.currentLog().addMacro(pTaken, pTakenBody)

          val newChunk = ch.withPerm(PermMinus(ch.perm, pTaken))
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
      val interpreter = new NonQuantifiedPropertyInterpreter(allChunks, v)
      newChunks foreach { ch =>
        val resource = Resources.resourceDescriptions(ch.resourceID)
        v.decider.assume(interpreter.buildPathConditionsForChunk(ch, resource.instanceProperties))
      }
      val newHeap = Heap(allChunks)

      val s0 = s.copy(functionRecorder = currentFunctionRecorder)

      summarise(s0, relevantChunks, resource, args, v)((s1, snap, _, _, v1) =>
        if (!moreNeeded) {
          if (!consumeExact) {
            v1.decider.assume(PermLess(perms, pSum))
          }
          Q(s1, newHeap, Some(snap), v1)
        } else {
          val toAssert = if (consumeExact) pNeeded === NoPerm() else IsPositive(pSum)
          v1.decider.assert(toAssert) {
            case true =>
              if (!consumeExact) {
                v1.decider.assume(PermLess(perms, pSum))
              }
              Q(s1, newHeap, Some(snap), v1)
            case false =>
              Failure(ve).withLoad(args)
          }
        })
    }
  }

  private val freeReceiver = Var(Identifier("?rcvr"), sorts.Ref)

  def assumeFieldPermissionUpperBounds(s: State, h: Heap, v: Verifier): Unit = {
    // TODO: Instead of "manually" assuming such upper bounds, appropriate PropertyInterpreters
    //       should be used, see StateConsolidator
    val relevantChunksPerField = MMap.empty[String, MList[BasicChunk]]

    // TODO: Consider caching results, e.g. as mapping from relevant chunks to permission sum

    h.values foreach {
      case ch: BasicChunk if ch.resourceID == FieldID =>
        val relevantChunks = relevantChunksPerField.getOrElseUpdate(ch.id.name, MList.empty)
        relevantChunks += ch
      case _ => /* Ignore */
    }

    relevantChunksPerField foreach { case (_, relevantChunks) =>
      val permissionSum =
        relevantChunks.foldLeft(NoPerm(): Term) { case (permSum, chunk) =>
          val eq = freeReceiver === chunk.args.head /* For field chunks, the receiver is the only argument */
          PermPlus(permSum, Ite(eq, chunk.perm, NoPerm()))
        }

      relevantChunks foreach (chunk => {
        val instantiatedPermSum = permissionSum.replace(freeReceiver, chunk.args.head)
        v.decider.assume(PermAtMost(instantiatedPermSum, FullPerm()))
      })
    }
  }
}
