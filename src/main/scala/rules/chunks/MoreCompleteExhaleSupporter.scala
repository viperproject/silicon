// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.rules.chunks

import viper.silicon.rules.chunks.chunkSupporter.findChunksWithID
import viper.silicon.interfaces.state._
import viper.silicon.interfaces.{Success, Unreachable, VerificationResult}
import viper.silicon.resources.{FieldID, NonQuantifiedPropertyInterpreter, Resources}
import viper.silicon.rules.{Complete, ConsumptionResult, ConsumptionRules, Incomplete, SnapshotMapDefinition, SymbolicExecutionRules, magicWandSupporter}
import viper.silicon.state._
import viper.silicon.state.terms._
import viper.silicon.state.terms.perms.{IsNonPositive, IsPositive}
import viper.silicon.supporters.functions.NoopFunctionRecorder
import viper.silicon.verifier.Verifier
import viper.silicon.{MList, MMap}
import viper.silver.ast
import viper.silver.verifier.VerificationError

import scala.collection.mutable.ListBuffer

object moreCompleteExhaleSupporter extends SymbolicExecutionRules {
  sealed trait TaggedSummarisingSnapshot {
    def snapshot: Term
  }

  final case class FreshSummarisingSnapshot(snapshot: Term) extends TaggedSummarisingSnapshot
  final case class ReusedSummarisingSnapshot(snapshot: Term) extends TaggedSummarisingSnapshot

  private def summariseOnly(s: State,
                            relevantChunks: Seq[NonQuantifiedChunk],
                            resource: ast.Resource,
                            args: Seq[Term],
                            knownValue: Option[Option[Term]],
                            v: Verifier)
                           : (State, TaggedSummarisingSnapshot, Seq[Term], Term) = {

    // TODO: Since relevantChunks is a sequence, the order of the chunks affects caching, but shouldn't.
    //       An order-agnostic way of caching, would be better. A simple benchmark should reveal how
    //       many cache misses are due to order changes.

    // TODO: Caching would be more effective if the summary were created independently of the provided
    //       args. E.g. the summary could be created with free arguments ?a1, ?a2, ...; this summary
    //       could be cached, and ?a1 etc. would be replaced before returning the summary to the caller.

    Verifier.config.mapCache(s.ssCache.get((resource, relevantChunks, args))) match {
      case Some((_taggedSummarisingSnapshot, _summarisingSnapshotDefinitions, _permissionSum)) =>
        return (s, _taggedSummarisingSnapshot, _summarisingSnapshotDefinitions, _permissionSum)
      case _ =>
        /* Cache miss */
    }

    val sort: Sort =
      resource match {
        case f: ast.Field => v.symbolConverter.toSort(f.typ)
        case _: ast.Predicate => sorts.Snap
        case _: ast.MagicWand => sorts.MagicWandSnapFunction
      }

    val `?s` = Var(Identifier("?s"), sort, false)
    var summarisingSnapshotDefinitions: Seq[Term] = Vector.empty
    var permissionSum: Term = NoPerm

    relevantChunks.foreach(ch => {
      val argumentEqualities =
        And(ch.args.zip(args).map { case (t1, t2) => t1 === t2 })

      summarisingSnapshotDefinitions :+=
        Implies(And(argumentEqualities, IsPositive(ch.perm)), `?s` === ch.snap)

      permissionSum =
        PermPlus(permissionSum, Ite(argumentEqualities, ch.perm, NoPerm))
    })

    val taggedSummarisingSnapshot =
      summarisingSnapshotDefinitions
        .collectFirst {
          case Equals(`?s`, snap) =>
            ReusedSummarisingSnapshot(snap)
        }.getOrElse({
          knownValue match {
            case Some(Some(v)) =>
              ReusedSummarisingSnapshot(v)
            case _ =>
              val definiteAliasValue = knownValue match {
                case None =>
                  // We have not yet checked for a definite alias
                  val id = ChunkIdentifier(resource, s.program)
                  val potentialAlias = chunkSupporter.findChunk[NonQuantifiedChunk](relevantChunks, id, args, v)
                  potentialAlias.filter(c => v.decider.check(IsPositive(c.perm), Verifier.config.checkTimeout())).map(_.snap)
                case Some(v) =>
                  // We have checked for a definite alias and may or may not have found one.
                  v
              }
              definiteAliasValue match {
                case Some(v) =>
                  ReusedSummarisingSnapshot(v)
                case None =>
                  val ss = v.decider.appliedFresh("ss", sort, s.functionRecorderQuantifiedVariables())
                  FreshSummarisingSnapshot(ss)
              }
          }
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
                        knownValue: Option[Option[Term]], // None if we have not yet checked for a definite alias,
                                                          // Some(v) if we have checked and the result was v
                        v: Verifier)
                       (Q: (State, Term, Seq[Term], Term, Verifier) => VerificationResult)
                       : VerificationResult = {
    // Don't use the shortcut if we want a counterexample; in that case, we need the decider to perform a single
    // query to check if the permission amount we have is sufficient to get the correct counterexample. If we perform
    // the query in two parts (one part here, one part in our caller to see if the permission amount is sufficient),
    // the counterexample might be wrong.
    if (relevantChunks.size == 1 &&  !Verifier.config.counterexample.isDefined) {
      val chunk = relevantChunks.head
      if (v.decider.check(And(chunk.args.zip(args).map { case (t1, t2) => t1 === t2 }), Verifier.config.checkTimeout())) {
        return Q(s, chunk.snap, Seq(), chunk.perm, v)
      } else {
        return Q(s, chunk.snap, Seq(), NoPerm, v)
      }
    }
    val (s1, taggedSnap, snapDefs, permSum) = summariseOnly(s, relevantChunks, resource, args, knownValue, v)

    v.decider.assumeDefinition(And(snapDefs))
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


    val id = ChunkIdentifier(resource, s.program)
    val relevantChunks = findChunksWithID[NonQuantifiedChunk](h.values, id).toSeq

    if (relevantChunks.isEmpty) {
      if (v.decider.checkSmoke(true)) {
        Success() // TODO: Mark branch as dead?
      } else {
        createFailure(ve, v, s)
      }
    } else {
      summarise(s, relevantChunks, resource, args, None, v)((s1, snap, _, permSum, v1) =>
        v.decider.assert(IsPositive(permSum), s1) {
          case true =>
            Q(s1, snap, v1)
          case false =>
            createFailure(ve, v, s1)
        })
    }
  }

  def consumeComplete(s: State,
                      h: Heap,
                      resource: ast.Resource,
                      args: Seq[Term],
                      perms: Term,
                      ve: VerificationError,
                      v: Verifier,
                      isFinalHeap: Boolean)
                     (Q: (State, Heap, Heap, Option[Term], Verifier) => VerificationResult)
                     : VerificationResult = {

    if (!s.hackIssue387DisablePermissionConsumption)
      actualConsumeComplete(s, h, resource, args, perms, ve, v, isFinalHeap)(Q)
    else
      ??? // summariseHeapAndAssertReadAccess(s, h, resource, args, ve, v)(Q)
  }

  private def summariseHeapAndAssertReadAccess(s: State,
                                               h: Heap,
                                               resource: ast.Resource,
                                               args: Seq[Term],
                                               ve: VerificationError,
                                               v: Verifier)
                                              (Q: (State, Heap, Option[Term], Verifier) => VerificationResult)
                                              : VerificationResult = {

    val id = ChunkIdentifier(resource, s.program)
    val relevantChunks = findChunksWithID[NonQuantifiedChunk](h.values, id).toSeq

    summarise(s, relevantChunks, resource, args, None, v)((s1, snap, _, permSum, v1) =>
      v.decider.assert(IsPositive(permSum), s1) {
        case true =>
          Q(s1, h, Some(snap), v1)
        case false =>
          createFailure(ve, v, s1)
      })
  }

  def consumeSingle(resource: ast.Resource, args: Seq[Term], ve: VerificationError)(s: State, h: Heap, perms: Term, v: Verifier, isFinalHeap: Boolean): (ConsumptionResult, State, Heap, Heap, Option[Chunk]) = {
    doActualConsumeComplete2(s, h, resource, args, perms, ve, v)
  }

  def consumeSingleWithLoopStuff(resource: ast.Resource, args: Seq[Term], ve: VerificationError)(s: State, h: Heap, perms: Term, v: Verifier, isFinalHeap: Boolean): (ConsumptionResult, State, Heap, Heap, Option[Chunk]) = {
    if (!isFinalHeap) {
      doActualConsumeComplete2(s, h, resource, args, perms, ve, v)
    } else {
      var res: (ConsumptionResult, State, Heap, Heap, Option[Chunk]) = null
      actualConsumeComplete(s, h, resource, args, perms, ve, v, isFinalHeap)((s2, h2, cHeap2, optSnap, v2) => {
        val cChunk = optSnap match {
          case Some(snap) => resource match {
            case mw: ast.MagicWand => Some(MagicWandChunk(MagicWandIdentifier(mw, s.program), Map(), args, snap.asInstanceOf[MagicWandSnapshot], perms))
            case _ => Some(BasicChunk(FieldID, ChunkIdentifier(resource, s.program).asInstanceOf[BasicChunkIdentifier], args, snap, perms))
          }
          case None => None
        }
        res = (Complete(), s2, h2, cHeap2, cChunk)
        Success()
      })
      if (res != null) {
        res
      } else {
        (Incomplete(perms), s,h, Heap(), None) // Garbage values??
      }
    }
  }

  private def actualConsumeComplete(s: State,
                                    h: Heap,
                                    resource: ast.Resource,
                                    args: Seq[Term],
                                    perms: Term,
                                    ve: VerificationError,
                                    v: Verifier,
                                    isFinalHeap: Boolean)
                                   (Q: (State, Heap, Heap, Option[Term], Verifier) => VerificationResult)
  : VerificationResult = {
    if (s.loopPhaseStack.nonEmpty && s.loopPhaseStack.head._1 != LoopPhases.Checking && isFinalHeap) {
      if (s.loopPhaseStack.head._1 == LoopPhases.Transferring) {
        val heaps = Seq(h) ++ s.loopHeapStack
        val failure = createFailure(ve, v, s)

        //def consumeSingle(s: State, h: Heap, perms: Term, v: Verifier): (ConsumptionResult, State, Heap, Heap, Option[Chunk]) = {
        //  doActualConsumeComplete2(s, h, resource, args, perms, ve, v)
        //}

        magicWandSupporter.consumeFromMultipleHeapsKInd(s, heaps, perms, failure, Seq(), v)(consumeSingle(resource, args, ve))((s1, hs1, cHeap1, optChunks, v1) => {
          //val (fr1, newTopHeap) = v1.stateConsolidator(s1).merge(s1.functionRecorder, s1.h, cHeap1, v1)
          //val (fr1, newTopHeap) = (s1.functionRecorder, s1.h + cHeap1)
          val totalConsumedAmount = perms
          val totalConsumedFromFirst = if (optChunks.length > 0 && optChunks.head.nonEmpty) {
            PermMin(optChunks.head.get.asInstanceOf[NonQuantifiedChunk].perm, totalConsumedAmount)
          } else {
            NoPerm
          }
          val totalConsumedFromAllButFirst = PermMinus(totalConsumedAmount, totalConsumedFromFirst)


          val nonEmptyChunks = optChunks.filter(_.isDefined)
          val cHeap2 = if (nonEmptyChunks.isEmpty)
            Heap()
          else
            Heap(Seq(nonEmptyChunks.head.get.asInstanceOf[NonQuantifiedChunk].withPerm(totalConsumedFromAllButFirst)))
          val (fr1, newTopHeap2) = if (nonEmptyChunks.isEmpty || totalConsumedFromAllButFirst == NoPerm)
            (s1.functionRecorder, s1.h)
          else
            v1.stateConsolidator(s1).merge(s1.functionRecorder, s1, s1.h, cHeap2, v1)

          val s1p = s1.copy(loopHeapStack = hs1.tail, h = newTopHeap2, functionRecorder = fr1)
          if (nonEmptyChunks.isEmpty){
            assert(v1.decider.check(perms === NoPerm, 0))
            if (v1.decider.checkSmoke(false))
              Success()
            else
              Q(s1p, hs1.head, cHeap2, None, v1)
          } else {
            Q(s1p, hs1.head, cHeap2, nonEmptyChunks.head.map(_.asInstanceOf[NonQuantifiedChunk].snap), v1)
          }
        })
      } else {
        // TODO: Try actual consume complete
        val identifier = resource match {
          case f: ast.Field => BasicChunkIdentifier(f.name)
          case p: ast.Predicate => BasicChunkIdentifier(p.name)
          case mw: ast.MagicWand => MagicWandIdentifier(mw, s.program)
        }
        val chs = chunkSupporter.findChunksWithID[NonQuantifiedChunk](h.values, identifier)
        val currentPermAmount =
          chs.foldLeft(NoPerm: Term)((q, ch) => {
            val argsPairWiseEqual = And(args.zip(ch.args).map { case (a1, a2) => a1 === a2 })
            PermPlus(q, Ite(argsPairWiseEqual, ch.perm, NoPerm))
          })
        val maxGain = PermMinus(perms, currentPermAmount)
        val gain = PermMax(maxGain, NoPerm)
        val snapSort = resource match {
          case f: ast.Field => v.symbolConverter.toSort(f.typ)
          case p: ast.Predicate => p.body.map(v.snapshotSupporter.optimalSnapshotSort(_, s.program)._1)
            .getOrElse(sorts.Snap)
          case _ => sorts.Snap
        }

        val ch = identifier match {
          case mwi: MagicWandIdentifier =>
            val snap = MagicWandSnapshot(v.decider.fresh(sorts.MagicWandSnapFunction))//v.decider.fresh(snapSort)
            MagicWandChunk(mwi, Map(), args, snap, gain)
          case bci: BasicChunkIdentifier =>
            val snap = v.decider.fresh(snapSort)
            BasicChunk(FieldID, bci, args, snap, gain)
        }

        chunkSupporter.produce(s, h, ch, v)((s2, h2, v2) => {
          val (fr3, s3h) = v2.stateConsolidator(s2).merge(s2.functionRecorder, s2, s2.h, ch, v2)
          doActualConsumeComplete(s2.copy(h = s3h, functionRecorder = fr3), h2, resource, args, perms, ve, v2)(Q)
        })
      }
    } else {
      doActualConsumeComplete(s, h, resource, args, perms, ve, v)(Q)
    }
  }

  private def doActualConsumeComplete2(s: State,
                                      h: Heap,
                                      resource: ast.Resource,
                                      args: Seq[Term],
                                      perms: Term,
                                      ve: VerificationError,
                                      v: Verifier)
  : (ConsumptionResult, State, Heap, Heap, Option[Chunk]) = {

    val id = ChunkIdentifier(resource, s.program)
    val relevantChunks = ListBuffer[NonQuantifiedChunk]()
    val otherChunks = ListBuffer[Chunk]()
    h.values foreach {
      case c: NonQuantifiedChunk if id == c.id => relevantChunks.append(c)
      case ch => otherChunks.append(ch)
    }

    if (relevantChunks.isEmpty) {
      // if no permission is exhaled, return none
      v.decider.check(perms === NoPerm, Verifier.config.assertTimeout.getOrElse(0)) match {
        case true => (Complete(), s, h, Heap(), None) // Q(s, h, Heap(), None, v)
        case false => (Incomplete(perms), s, h, Heap(), None)
      }
    } else {
      val constrainableVars = s.constrainableARPs ++ (if (s.loopPhaseStack.nonEmpty && s.loopPhaseStack.head._1 == LoopPhases.Transferring && s.loopReadVarStack.head._2) Seq(s.loopReadVarStack.head._1) else Seq())
      if (!terms.utils.consumeExactRead(perms, constrainableVars)) {
        var res: (ConsumptionResult, State, Heap, Heap, Option[Chunk]) = (Incomplete(perms), s, h, Heap(), None)
        actualConsumeCompleteConstrainable(s, relevantChunks, resource, args, perms, ve, v)((s1, updatedChunks, consumedChunks, optSnap, v2) => {
          //Q(s1, Heap(updatedChunks ++ otherChunks), Heap(consumedChunks), optSnap, v2)
          val consumedChunk = Some(consumedChunks.head.withSnap(optSnap.get).withPerm(perms).withArgs(args))
          res = (Complete(), s1, Heap(updatedChunks ++ otherChunks), Heap(consumedChunks), consumedChunk)
          Success()
        })
        res
      } else {
        var pNeeded = perms
        var pSum: Term = NoPerm
        val newChunks = ListBuffer[NonQuantifiedChunk]()
        val consumedChunks = ListBuffer[NonQuantifiedChunk]()
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

            val pTaken = if (s.functionRecorder != NoopFunctionRecorder || Verifier.config.useFlyweight) { // needed for kinduct
              // ME: When using Z3 via API, it is beneficial to not use macros, since macro-terms will *always* be different
              // (leading to new terms that have to be translated), whereas without macros, we can usually use a term
              // that already exists.
              // During function verification, we should not define macros, since they could contain resullt, which is not
              // defined elsewhere.
              Ite(eq, PermMin(ch.perm, pNeeded), NoPerm)
            } else {
              val pTakenBody = Ite(eq, PermMin(ch.perm, pNeeded), NoPerm)
              val pTakenArgs = additionalArgs
              val pTakenDecl = v.decider.freshMacro("mce_pTaken", pTakenArgs, pTakenBody)
              val pTakenMacro = Macro(pTakenDecl.id, pTakenDecl.args.map(_.sort), pTakenDecl.body.sort)
              currentFunctionRecorder = currentFunctionRecorder.recordFreshMacro(pTakenDecl)
              val pTakenApp = App(pTakenMacro, pTakenArgs)
              v.symbExLog.addMacro(pTakenApp, pTakenBody)
              pTakenApp
            }

            if (v.decider.check(Not(eq), Verifier.config.checkTimeout())) {
              newChunks.append(ch)
            } else {
              pSum = PermPlus(pSum, Ite(eq, ch.perm, NoPerm))

              val newChunk = ch.withPerm(PermMinus(ch.perm, pTaken))
              pNeeded = PermMinus(pNeeded, pTaken)
              val consumedChunk = ch.withPerm(pTaken)

              if (!v.decider.check(pTaken === NoPerm, Verifier.config.splitTimeout())) {
                consumedChunks.append(consumedChunk)
              }

              if (!v.decider.check(IsNonPositive(newChunk.perm), Verifier.config.splitTimeout())) {
                newChunks.append(newChunk)
              }

              moreNeeded = !v.decider.check(pNeeded === NoPerm, Verifier.config.splitTimeout())
            }
          } else {
            newChunks.append(ch)
          }
        }

        val allChunks = otherChunks ++ newChunks
        // TODO: Since no permissions were gained, I don't see why the PropertyInterpreter would yield any new assumptions.
        //       See if it can be removed here.
        val interpreter = new NonQuantifiedPropertyInterpreter(allChunks, v, s)
        newChunks foreach { ch =>
          val resource = Resources.resourceDescriptions(ch.resourceID)
          v.decider.assume(interpreter.buildPathConditionsForChunk(ch, resource.instanceProperties))
        }
        val newHeap = Heap(allChunks)
        val consumedHeap = Heap(consumedChunks)

        val s0 = s.copy(functionRecorder = currentFunctionRecorder)

        var result: (ConsumptionResult, State, Heap, Heap, Option[Chunk]) = null
        summarise(s0, relevantChunks.toSeq, resource, args, None, v)((s1, snap, _, _, v1) => {
          val condSnap = if (v1.decider.check(IsPositive(perms), Verifier.config.checkTimeout())) {
            snap
          } else {
            Ite(IsPositive(perms), snap.convert(sorts.Snap), Unit).convert(snap.sort)
          }
          if (!moreNeeded) {
            val consumedChunk = Some(consumedChunks.head.withSnap(condSnap).withPerm(perms).withArgs(args))
            result = (Complete(), s1, newHeap, consumedHeap, consumedChunk)//Q(s1, newHeap, consumedHeap, Some(condSnap), v1)
            Success()
          } else {
            v1.decider.assert(pNeeded === NoPerm, s1) {
              case true =>
                val consumedChunk = Some(consumedChunks.head.withSnap(condSnap).withPerm(perms).withArgs(args))
                result = (Complete(), s1, newHeap, consumedHeap, consumedChunk)
                //Q(s1, newHeap, consumedHeap, Some(condSnap), v1)
                Success()
              case false =>
                val consumedChunk = if (consumedChunks.isEmpty) None else Some(consumedChunks.head.withSnap(condSnap).withPerm(PermMinus(perms, pNeeded)).withArgs(args))
                result = (Incomplete(pNeeded), s1, newHeap, consumedHeap, consumedChunk)
                //Q(s1, newHeap, consumedHeap, Some(condSnap), v1)
                Success()
            }
          }
        })
        result
      }
    }
  }

  private def doActualConsumeComplete(s: State,
                                    h: Heap,
                                    resource: ast.Resource,
                                    args: Seq[Term],
                                    perms: Term,
                                    ve: VerificationError,
                                    v: Verifier)
                                   (Q: (State, Heap, Heap, Option[Term], Verifier) => VerificationResult)
                                   : VerificationResult = {

    val id = ChunkIdentifier(resource, s.program)
    val relevantChunks = ListBuffer[NonQuantifiedChunk]()
    val otherChunks = ListBuffer[Chunk]()
    h.values foreach {
      case c: NonQuantifiedChunk if id == c.id => relevantChunks.append(c)
      case ch => otherChunks.append(ch)
    }

    if (relevantChunks.isEmpty) {
      // if no permission is exhaled, return none
      v.decider.assert(perms === NoPerm, s) {
        case true => Q(s, h, Heap(), None, v)
        case false => createFailure(ve, v, s)
      }
    } else {
      val constrainableVars = s.constrainableARPs ++ (if (s.loopPhaseStack.nonEmpty && s.loopPhaseStack.head._1 == LoopPhases.Transferring && s.loopReadVarStack.head._2) Seq(s.loopReadVarStack.head._1) else Seq())
      if (!terms.utils.consumeExactRead(perms, constrainableVars)) {
        actualConsumeCompleteConstrainable(s, relevantChunks, resource, args, perms, ve, v)((s1, updatedChunks, consumedChunks, optSnap, v2) => {
          Q(s1, Heap(updatedChunks ++ otherChunks), Heap(consumedChunks), optSnap, v2)})
      } else {
        var pNeeded = perms
        var pSum: Term = NoPerm
        val newChunks = ListBuffer[NonQuantifiedChunk]()
        val consumedChunks = ListBuffer[NonQuantifiedChunk]()
        var moreNeeded = true

        val (sortedChunks, checkedDefiniteAlias) = if (relevantChunks.size < 2) {
          (relevantChunks, None)
        } else {
          val definiteAlias = chunkSupporter.findChunk[NonQuantifiedChunk](relevantChunks, id, args, v).filter(c =>
            v.decider.check(IsPositive(c.perm), Verifier.config.checkTimeout())
          )

          val sortFunction: (NonQuantifiedChunk, NonQuantifiedChunk) => Boolean = (ch1, ch2) => {
            // The definitive alias and syntactic aliases should get priority, since it is always
            // possible to consume from them
            definiteAlias.contains(ch1) || !definiteAlias.contains(ch2) && ch1.args == args
          }

          (relevantChunks.sortWith(sortFunction), Some(definiteAlias))
        }

        val additionalArgs = s.relevantQuantifiedVariables
        var currentFunctionRecorder = s.functionRecorder

        sortedChunks foreach { ch =>
          if (moreNeeded) {
            val eq = And(ch.args.zip(args).map { case (t1, t2) => t1 === t2 })

            val pTaken = if (true) { //s.functionRecorder != NoopFunctionRecorder || Verifier.config.useFlyweight) {
              // ME: When using Z3 via API, it is beneficial to not use macros, since macro-terms will *always* be different
              // (leading to new terms that have to be translated), whereas without macros, we can usually use a term
              // that already exists.
              // During function verification, we should not define macros, since they could contain resullt, which is not
              // defined elsewhere.
              Ite(eq, PermMin(ch.perm, pNeeded), NoPerm)
            } else {
              val pTakenBody = Ite(eq, PermMin(ch.perm, pNeeded), NoPerm)
              val pTakenArgs = additionalArgs
              val pTakenDecl = v.decider.freshMacro("mce_pTaken", pTakenArgs, pTakenBody)
              val pTakenMacro = Macro(pTakenDecl.id, pTakenDecl.args.map(_.sort), pTakenDecl.body.sort)
              currentFunctionRecorder = currentFunctionRecorder.recordFreshMacro(pTakenDecl)
              val pTakenApp = App(pTakenMacro, pTakenArgs)
              v.symbExLog.addMacro(pTakenApp, pTakenBody)
              pTakenApp
            }

            pSum = PermPlus(pSum, Ite(eq, ch.perm, NoPerm))

            val newChunk = ch.withPerm(PermMinus(ch.perm, pTaken))
            pNeeded = PermMinus(pNeeded, pTaken)
            val consumedChunk = ch.withPerm(pTaken)

            val noneTaken = pTaken=== NoPerm

            if (noneTaken == False || !v.decider.check(noneTaken, Verifier.config.splitTimeout())) {
              consumedChunks.append(consumedChunk)
            }

            val newChunkHasNoPerm = IsNonPositive(newChunk.perm)

            if (newChunkHasNoPerm == False || !v.decider.check(newChunkHasNoPerm, Verifier.config.splitTimeout())) {
              newChunks.append(newChunk)
            }

            val noMoreNeeded = pNeeded === NoPerm
            moreNeeded = noMoreNeeded == False || !v.decider.check(noMoreNeeded, Verifier.config.splitTimeout())
          } else {
            newChunks.append(ch)
          }
        }

        val allChunks = otherChunks ++ newChunks
        // TODO: Since no permissions were gained, I don't see why the PropertyInterpreter would yield any new assumptions.
        //       See if it can be removed here.
        val interpreter = new NonQuantifiedPropertyInterpreter(allChunks, v, s)
        newChunks foreach { ch =>
          val resource = Resources.resourceDescriptions(ch.resourceID)
          v.decider.assume(interpreter.buildPathConditionsForChunk(ch, resource.instanceProperties))
        }
        val newHeap = Heap(allChunks)
        val consumedHeap = Heap(consumedChunks)

        val s0 = s.copy(functionRecorder = currentFunctionRecorder)

        val checkedDefiniteValue = checkedDefiniteAlias.map(_.map(_.snap))

        summarise(s0, relevantChunks.toSeq, resource, args, checkedDefiniteValue, v)((s1, snap, _, _, v1) => {
          val condSnap = if (v1.decider.check(IsPositive(perms), Verifier.config.checkTimeout())) {
            snap
          } else {
            Ite(IsPositive(perms), snap.convert(sorts.Snap), Unit).convert(snap.sort)
          }
          if (!moreNeeded) {
            Q(s1, newHeap, consumedHeap, Some(condSnap), v1)
          } else {
            v1.decider.assert(pNeeded === NoPerm, s1) {
              case true =>
                Q(s1, newHeap, consumedHeap, Some(condSnap), v1)
              case false =>
                createFailure(ve, v1, s1)
            }
          }})
      }
    }
  }

  private def actualConsumeCompleteConstrainable(s: State,
                                                 relevantChunks: ListBuffer[NonQuantifiedChunk],
                                                 resource: ast.Resource,
                                                 args: Seq[Term],
                                                 perms: Term, // Expected to be constrainable. Will be assumed to equal the consumed permission amount.
                                                 ve: VerificationError,
                                                 v: Verifier)
                                                (Q: (State, ListBuffer[NonQuantifiedChunk], ListBuffer[NonQuantifiedChunk], Option[Term], Verifier) => VerificationResult)
                                                : VerificationResult = {

    var totalPermSum: Term = NoPerm
    var totalPermTaken: Term = NoPerm
    var newFr = s.functionRecorder

    var consumedChunks = ListBuffer[NonQuantifiedChunk]()

    val updatedChunks =
      relevantChunks map (ch => {
        val eq = And(ch.args.zip(args).map { case (t1, t2) => t1 === t2 })
        if (v.decider.check(Not(eq), Verifier.config.checkTimeout())) {
          ch
        } else {
          val permTaken = v.decider.fresh("p", sorts.Perm)

          totalPermSum = PermPlus(totalPermSum, Ite(eq, ch.perm, NoPerm))
          totalPermTaken = PermPlus(totalPermTaken, permTaken)

          val constraint = And(IsValidPermVar(permTaken),
            PermAtMost(permTaken, ch.perm),
            Implies(Not(eq), permTaken === NoPerm),
            Implies(And(eq, IsPositive(ch.perm)), PermLess(permTaken, ch.perm))
          )

          v.decider.assume(constraint)
          newFr = newFr.recordConstrainedVar(permTaken, constraint)
          consumedChunks.append(ch.withPerm(permTaken))
          ch.withPerm(PermMinus(ch.perm, permTaken))
        }
      })

    val totalTakenBounds =
      Implies(
        totalPermSum !== NoPerm,
        And(
          PermLess(NoPerm, totalPermTaken),
          PermLess(totalPermTaken, totalPermSum)))
    v.decider.assume(totalTakenBounds)

    newFr = newFr.recordConstraint(totalTakenBounds)

    val s1 = s.copy(functionRecorder = newFr)

    v.decider.assert(totalPermTaken !== NoPerm, s1) {
      case true =>
        v.decider.assume(perms === totalPermTaken)
        summarise(s1, relevantChunks.toSeq, resource, args, None, v)((s2, snap, _, _, v1) =>
          Q(s2, updatedChunks, consumedChunks, Some(snap), v1))
      case false =>
        createFailure(ve, v, s)
    }
  }


  private val freeReceiver = Var(Identifier("?rcvr"), sorts.Ref, false)

  def assumeFieldPermissionUpperBounds(h: Heap, v: Verifier): Unit = {
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
        relevantChunks.foldLeft(NoPerm: Term) { case (permSum, chunk) =>
          val eq = freeReceiver === chunk.args.head /* For field chunks, the receiver is the only argument */
          PermPlus(permSum, Ite(eq, chunk.perm, NoPerm))
        }

      relevantChunks foreach (chunk => {
        val instantiatedPermSum = permissionSum.replace(freeReceiver, chunk.args.head)
        v.decider.assume(PermAtMost(instantiatedPermSum, FullPerm))
      })
    }
  }
}
