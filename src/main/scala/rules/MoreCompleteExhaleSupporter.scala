// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.rules

import debugger.DebugExp
import viper.silicon.interfaces.state._
import viper.silicon.interfaces.{Success, VerificationResult}
import viper.silicon.resources.{FieldID, NonQuantifiedPropertyInterpreter, Resources}
import viper.silicon.rules.chunkSupporter.findChunksWithID
import viper.silicon.state._
import viper.silicon.state.terms._
import viper.silicon.state.terms.perms.{IsNonPositive, IsPositive}
import viper.silicon.supporters.functions.NoopFunctionRecorder
import viper.silicon.utils.ast.{BigAnd, buildMinExp, removeKnownToBeTrueExp, simplifyVariableName}
import viper.silicon.verifier.Verifier
import viper.silicon.{MList, MMap}
import viper.silver.ast
import viper.silver.parser.PPrimitiv
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
                            argsExp: Seq[ast.Exp],
                            v: Verifier)
                           : (State, TaggedSummarisingSnapshot, Seq[Term], Term, ast.Exp) = {

    // TODO: Since relevantChunks is a sequence, the order of the chunks affects caching, but shouldn't.
    //       An order-agnostic way of caching, would be better. A simple benchmark should reveal how
    //       many cache misses are due to order changes.

    // TODO: Caching would be more effective if the summary were created independently of the provided
    //       args. E.g. the summary could be created with free arguments ?a1, ?a2, ...; this summary
    //       could be cached, and ?a1 etc. would be replaced before returning the summary to the caller.

    Verifier.config.mapCache(s.ssCache.get((resource, relevantChunks, args))) match {
      case Some((_taggedSummarisingSnapshot, _summarisingSnapshotDefinitions, _permissionSum, _permissionSumExp)) =>
        return (s, _taggedSummarisingSnapshot, _summarisingSnapshotDefinitions, _permissionSum, _permissionSumExp)
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
    var permissionSum: Term = NoPerm
    var permissionSumExp: ast.Exp = ast.NoPerm()()

    relevantChunks.foreach(ch => {
      val argumentEqualities =
        And(ch.args.zip(args).map { case (t1, t2) => t1 === t2 })
      val argumentEqualitiesExp =
        BigAnd(ch.argsExp.zip(argsExp).map { case (e1, e2) => ast.EqCmp(e1, e2)() })

      summarisingSnapshotDefinitions :+=
        Implies(And(argumentEqualities, IsPositive(ch.perm)), `?s` === ch.snap)

      permissionSum =
        PermPlus(permissionSum, Ite(argumentEqualities, ch.perm, NoPerm))

      permissionSumExp =
        ast.PermAdd(permissionSumExp, ast.CondExp(argumentEqualitiesExp, ch.permExp, ast.NoPerm()())())()
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

    val ssc1 = s.ssCache + ((resource, relevantChunks, args) -> (taggedSummarisingSnapshot, summarisingSnapshotDefinitions, permissionSum, permissionSumExp))
    val s1 = s.copy(ssCache = ssc1)

    (s1, taggedSummarisingSnapshot, summarisingSnapshotDefinitions, permissionSum, permissionSumExp)
  }

  private def summarise(s: State,
                        relevantChunks: Seq[NonQuantifiedChunk],
                        resource: ast.Resource,
                        args: Seq[Term],
                        argsExp: Seq[ast.Exp],
                        v: Verifier)
                       (Q: (State, Term, Seq[Term], Term, ast.Exp, Verifier) => VerificationResult)
                       : VerificationResult = {
    // Don't use the shortcut if we want a counterexample; in that case, we need the decider to perform a single
    // query to check if the permission amount we have is sufficient to get the correct counterexample. If we perform
    // the query in two parts (one part here, one part in our caller to see if the permission amount is sufficient),
    // the counterexample might be wrong.
    if (relevantChunks.size == 1 &&  !Verifier.config.counterexample.isDefined) {
      val chunk = relevantChunks.head
      if (v.decider.check(And(chunk.args.zip(args).map { case (t1, t2) => t1 === t2 }), Verifier.config.checkTimeout())) {
        return Q(s, chunk.snap, Seq(), chunk.perm, chunk.permExp, v)
      } else {
        return Q(s, chunk.snap, Seq(), NoPerm, ast.NoPerm()(), v)
      }
    }
    val (s1, taggedSnap, snapDefs, permSum, permSumExp) = summariseOnly(s, relevantChunks, resource, args, argsExp, v)

    v.decider.assume(And(snapDefs), DebugExp.createInstance("Snapshot", true))
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

    Q(s2, taggedSnap.snapshot, snapDefs, permSum, permSumExp, v)
  }

  def lookupComplete(s: State,
                     h: Heap,
                     resource: ast.Resource,
                     args: Seq[Term],
                     argsExp: Seq[ast.Exp],
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
        createFailure(ve, v, s, None)
      }
    } else {
      summarise(s, relevantChunks, resource, args, argsExp, v)((s1, snap, _, permSum, permSumExp, v1) =>
        v.decider.assert(IsPositive(permSum)) {
          case true =>
            Q(s1, snap, v1)
          case false =>
            createFailure(ve, v, s1, Some(ast.GtCmp(permSumExp, ast.IntLit(0)())()))
        })
    }
  }

  def consumeComplete(s: State,
                      h: Heap,
                      resource: ast.Resource,
                      args: Seq[Term],
                      argsExp: Seq[ast.Exp],
                      perms: Term,
                      permsExp: ast.Exp,
                      ve: VerificationError,
                      v: Verifier)
                     (Q: (State, Heap, Option[Term], Verifier) => VerificationResult)
                     : VerificationResult = {

    if (!s.hackIssue387DisablePermissionConsumption)
      actualConsumeComplete(s, h, resource, args, argsExp, perms, permsExp, ve, v)(Q)
    else
      summariseHeapAndAssertReadAccess(s, h, resource, args, argsExp, ve, v)(Q)
  }

  private def summariseHeapAndAssertReadAccess(s: State,
                                               h: Heap,
                                               resource: ast.Resource,
                                               args: Seq[Term],
                                               argsExp: Seq[ast.Exp],
                                               ve: VerificationError,
                                               v: Verifier)
                                              (Q: (State, Heap, Option[Term], Verifier) => VerificationResult)
                                              : VerificationResult = {

    val id = ChunkIdentifier(resource, s.program)
    val relevantChunks = findChunksWithID[NonQuantifiedChunk](h.values, id).toSeq

    summarise(s, relevantChunks, resource, args, argsExp, v)((s1, snap, _, permSum, permSumExp, v1) =>
      v.decider.assert(IsPositive(permSum)) {
        case true =>
          Q(s1, h, Some(snap), v1)
        case false =>
          createFailure(ve, v, s1, Some(ast.GtCmp(permSumExp, ast.IntLit(0)())()))
      })
  }

  private def actualConsumeComplete(s: State,
                                    h: Heap,
                                    resource: ast.Resource,
                                    args: Seq[Term],
                                    argsExp: Seq[ast.Exp],
                                    perms: Term,
                                    permsExp: ast.Exp,
                                    ve: VerificationError,
                                    v: Verifier)
                                   (Q: (State, Heap, Option[Term], Verifier) => VerificationResult)
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
      v.decider.assert(perms === NoPerm) {
        case true => Q(s, h, None, v)
        case false => createFailure(ve, v, s, Some(ast.EqCmp(permsExp, ast.NoPerm()())(permsExp.pos, permsExp.info, permsExp.errT)))
      }
    } else {
      if (!terms.utils.consumeExactRead(perms, s.constrainableARPs)) {
        actualConsumeCompleteConstrainable(s, relevantChunks, resource, args, argsExp, perms, permsExp, ve, v)((s1, updatedChunks, optSnap, v2) => {
          Q(s1, Heap(updatedChunks ++ otherChunks), optSnap, v2)})
      } else {
        var pNeeded = perms
        var pNeededExp = permsExp
        var pSum: Term = NoPerm
        var pSumExp: ast.Exp = ast.NoPerm()(permsExp.pos, permsExp.info, permsExp.errT)
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
            val eqHelper = ch.args.zip(args).map { case (t1, t2) => t1 === t2 }
            val eq = And(eqHelper)
            val eqExp = BigAnd(removeKnownToBeTrueExp(ch.argsExp.zip(argsExp).map { case (t1, t2) => ast.EqCmp(t1, t2)(permsExp.pos, permsExp.info, permsExp.errT) }.toList, eqHelper.toList))

            val (pTaken, pTakenExp) = if (s.functionRecorder != NoopFunctionRecorder || Verifier.config.useFlyweight) {
              // ME: When using Z3 via API, it is beneficial to not use macros, since macro-terms will *always* be different
              // (leading to new terms that have to be translated), whereas without macros, we can usually use a term
              // that already exists.
              // During function verification, we should not define macros, since they could contain resullt, which is not
              // defined elsewhere.
              val iteExp = ast.CondExp(eqExp, buildMinExp(Seq(ch.permExp, pNeededExp), ast.Perm), ast.NoPerm()(permsExp.pos, permsExp.info, permsExp.errT))(eqExp.pos, eqExp.info, eqExp.errT)
              (Ite(eq, PermMin(ch.perm, pNeeded), NoPerm), iteExp)
            } else {
              val pTakenBody = Ite(eq, PermMin(ch.perm, pNeeded), NoPerm)
              val pTakenExp = ast.CondExp(eqExp, buildMinExp(Seq(ch.permExp, pNeededExp), ast.Perm), ast.NoPerm()())(eqExp.pos, eqExp.info, eqExp.errT)
              val pTakenArgs = additionalArgs
              val pTakenDecl = v.decider.freshMacro("mce_pTaken", pTakenArgs, pTakenBody)
              val pTakenMacro = Macro(pTakenDecl.id, pTakenDecl.args.map(_.sort), pTakenDecl.body.sort)
              currentFunctionRecorder = currentFunctionRecorder.recordFreshMacro(pTakenDecl)
              val pTakenApp = App(pTakenMacro, pTakenArgs)
              v.symbExLog.addMacro(pTakenApp, pTakenBody)
              (pTakenApp, pTakenExp)
            }

            pSum = PermPlus(pSum, Ite(eq, ch.perm, NoPerm))
            pSumExp = ast.PermAdd(pSumExp, ast.CondExp(eqExp, ch.permExp, ast.NoPerm()())(eqExp.pos, eqExp.info, eqExp.errT))()

            val newChunk = ch.withPerm(PermMinus(ch.perm, pTaken), ast.PermSub(ch.permExp, pTakenExp)(permsExp.pos, permsExp.info, permsExp.errT))
            pNeeded = PermMinus(pNeeded, pTaken)
            pNeededExp = ast.PermSub(pNeededExp, pTakenExp)(permsExp.pos, permsExp.info, permsExp.errT)

            if (!v.decider.check(IsNonPositive(newChunk.perm), Verifier.config.splitTimeout())) {
              newChunks.append(newChunk)
            }

            moreNeeded = !v.decider.check(pNeeded === NoPerm, Verifier.config.splitTimeout())
          } else {
            newChunks.append(ch)
          }
        }

        val allChunks = otherChunks ++ newChunks
        // TODO: Since no permissions were gained, I don't see why the PropertyInterpreter would yield any new assumptions.
        //       See if it can be removed here.
        val interpreter = new NonQuantifiedPropertyInterpreter(allChunks, v)
        newChunks foreach { ch =>
          val resource = Resources.resourceDescriptions(ch.resourceID)
          val pathCond = interpreter.buildPathConditionsForChunk(ch, resource.instanceProperties)
          pathCond.foreach(p => v.decider.assume(p.getFirst, DebugExp.createInstance(p.getSecond, s.substituteVarsInExp(p.getSecond))))
        }
        val newHeap = Heap(allChunks)

        val s0 = s.copy(functionRecorder = currentFunctionRecorder)

        summarise(s0, relevantChunks.toSeq, resource, args, argsExp, v)((s1, snap, _, _, _, v1) => {
          val condSnap = if (v1.decider.check(IsPositive(perms), Verifier.config.checkTimeout())) {
            snap
          } else {
            Ite(IsPositive(perms), snap.convert(sorts.Snap), Unit)
          }
          if (!moreNeeded) {
            Q(s1, newHeap, Some(condSnap), v1)
          } else {
            v1.decider.assert(pNeeded === NoPerm) {
              case true =>
                Q(s1, newHeap, Some(condSnap), v1)
              case false =>
                createFailure(ve, v1, s1, Some(ast.EqCmp(pNeededExp, ast.NoPerm()())(pNeededExp.pos, pNeededExp.info, pNeededExp.errT)))
            }
          }})
      }
    }
  }

  private def actualConsumeCompleteConstrainable(s: State,
                                                 relevantChunks: ListBuffer[NonQuantifiedChunk],
                                                 resource: ast.Resource,
                                                 args: Seq[Term],
                                                 argsExp: Seq[ast.Exp],
                                                 perms: Term, // Expected to be constrainable. Will be assumed to equal the consumed permission amount.
                                                 permsExp: ast.Exp,
                                                 ve: VerificationError,
                                                 v: Verifier)
                                                (Q: (State, ListBuffer[NonQuantifiedChunk], Option[Term], Verifier) => VerificationResult)
                                                : VerificationResult = {

    v.decider.startDebugSubExp()

    var totalPermSum: Term = NoPerm
    var totalPermSumExp: ast.Exp = ast.NoPerm()()
    var totalPermTaken: Term = NoPerm
    var totalPermTakenExp: ast.Exp = ast.NoPerm()()
    var newFr = s.functionRecorder


    val updatedChunks =
      relevantChunks map (ch => {
        val eqCmps = ch.args.zip(args).map { case (t1, t2) => t1 === t2 }
        val eq = And(eqCmps)
        val eqExp = BigAnd(removeKnownToBeTrueExp(ch.argsExp.zip(argsExp).map{ case (t1, t2) => ast.EqCmp(t1, t2)(permsExp.pos, permsExp.info, permsExp.errT) }.toList, eqCmps.toList))
        val permTaken = v.decider.fresh("p", sorts.Perm, PPrimitiv("Perm")())
        val permTakenExp = ast.LocalVar(simplifyVariableName(permTaken.id.name), ast.Perm)(permsExp.pos, permsExp.info, permsExp.errT)

        totalPermSum = PermPlus(totalPermSum, Ite(eq, ch.perm, NoPerm))
        totalPermSumExp = ast.PermAdd(totalPermSumExp, ast.CondExp(eqExp, ch.permExp, ast.NoPerm()())(eqExp.pos, eqExp.info, eqExp.errT))(permsExp.pos, permsExp.info, permsExp.errT)
        totalPermTaken = PermPlus(totalPermTaken, permTaken)
        totalPermTakenExp = ast.PermAdd(totalPermTakenExp, permTakenExp)(permsExp.pos, permsExp.info, permsExp.errT)

        val constraintTerms = List(PermAtMost(permTaken, ch.perm), Implies(Not(eq), permTaken === NoPerm))
        val constraintExp = BigAnd(
          removeKnownToBeTrueExp(List(ast.PermLeCmp(permTakenExp, ch.permExp)(), ast.Implies(ast.Not(eqExp)(), ast.EqCmp(permTakenExp, ast.NoPerm()())())(permsExp.pos, permsExp.info, permsExp.errT)), constraintTerms))

        val constraint = And(IsValidPermVar(permTaken) :: constraintTerms)

        v.decider.assume(constraint, DebugExp.createInstance(constraintExp, s.substituteVarsInExp(constraintExp)))
        newFr = newFr.recordArp(permTaken, constraint)

        ch.withPerm(PermMinus(ch.perm, permTaken), ast.PermSub(ch.permExp, permTakenExp)(permsExp.pos, permsExp.info, permsExp.errT))
      })

    val rhsTerm = And(
      PermLess(NoPerm, totalPermTaken),
      PermLess(totalPermTaken, totalPermSum))
    val assmptTerm = totalPermSum !== NoPerm
    val constraint = Implies(assmptTerm, rhsTerm)
    val constraintExp = ast.Implies(ast.NeCmp(totalPermSumExp, ast.NoPerm()())(),
      ast.And(ast.PermLeCmp(ast.NoPerm()(), totalPermTakenExp)(), ast.PermLeCmp(totalPermTakenExp, totalPermSumExp)())(permsExp.pos, permsExp.info, permsExp.errT))()

    v.decider.assume(constraint, DebugExp.createInstance(constraintExp, s.substituteVarsInExp(constraintExp)))

    val s1 = s.copy(functionRecorder = newFr)

    v.decider.assert(totalPermTaken !== NoPerm) {
      case true =>
        val constraint = perms === totalPermTaken
        val constraintExp = ast.EqCmp(permsExp, totalPermTakenExp)()
        v.decider.assume(constraint, DebugExp.createInstance(constraintExp, s.substituteVarsInExp(constraintExp)))
        v.decider.finishDebugSubExp(s"consume permissions for ${resource.toString()}")
        summarise(s1, relevantChunks.toSeq, resource, args, argsExp, v)((s2, snap, _, _, _, v1) =>
          Q(s2, updatedChunks, Some(snap), v1))
      case false =>
        v.decider.finishDebugSubExp("consume permissions (failed)")
        createFailure(ve, v, s, Some(ast.NeCmp(totalPermTakenExp, ast.NoPerm()())()))
    }

  }


  private val freeReceiver = Var(Identifier("?rcvr"), sorts.Ref)

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
        val debugExp = DebugExp.createInstance("at most full perm") // FIXME ake: permissions
        v.decider.assume(PermAtMost(instantiatedPermSum, FullPerm), debugExp)
      })
    }
  }
}
