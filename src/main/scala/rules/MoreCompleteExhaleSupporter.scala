// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.rules

import viper.silicon.debugger.DebugExp
import viper.silicon.interfaces.state._
import viper.silicon.interfaces.{Success, VerificationResult}
import viper.silicon.resources.{FieldID, NonQuantifiedPropertyInterpreter, Resources}
import viper.silicon.rules.chunkSupporter.findChunksWithID
import viper.silicon.state._
import viper.silicon.state.terms._
import viper.silicon.state.terms.perms.{IsNonPositive, IsPositive}
import viper.silicon.supporters.functions.NoopFunctionRecorder
import viper.silicon.utils.ast.{BigAnd, buildMinExp, removeKnownToBeTrueExp, replaceVarsInExp, simplifyVariableName}
import viper.silicon.verifier.Verifier
import viper.silicon.{MList, MMap}
import viper.silver.ast
import viper.silver.parser.PUnknown
import viper.silver.verifier.VerificationError

import scala.collection.mutable.ListBuffer

object moreCompleteExhaleSupporter extends SymbolicExecutionRules {
  sealed trait TaggedSummarisingSnapshot {
    def snapshot: Term
  }

  final case class FreshSummarisingSnapshot(snapshot: Term) extends TaggedSummarisingSnapshot
  final case class ReusedSummarisingSnapshot(snapshot: Term) extends TaggedSummarisingSnapshot

  private def permSummariseOnly(s: State,
                            relevantChunks: Seq[NonQuantifiedChunk],
                            resource: ast.Resource,
                            args: Seq[Term],
                            argsExp: Option[Seq[ast.Exp]])
  : (State, Term, Option[ast.Exp]) = {
    Verifier.config.mapCache(s.ssCache.get((resource, relevantChunks, args))) match {
      case Some((_, _ ,_permissionSum, _permissionSumExp)) =>
        return (s, _permissionSum, _permissionSumExp)
      case _ =>
      /* Cache miss */
    }
    var permissionSum: Term = NoPerm
    var permissionSumExp: Option[ast.Exp] = Option.when(withExp)(ast.NoPerm()())
    relevantChunks.foreach(ch => {
      val argumentEqualities =
        And(ch.args.zip(args).map { case (t1, t2) => t1 === t2 })
      val argumentEqualitiesExp =
        Option.when(withExp)(BigAnd(ch.argsExp.get.zip(argsExp.get).map { case (e1, e2) => ast.EqCmp(e1, e2)() }))

      permissionSum =
        PermPlus(permissionSum, Ite(argumentEqualities, ch.perm, NoPerm))

      permissionSumExp = permissionSumExp.map(pse =>
        ast.PermAdd(pse, ast.CondExp(argumentEqualitiesExp.get, ch.permExp.get, ast.NoPerm()())())())
    })
    val ssc1 = s.ssCache + ((resource, relevantChunks, args) -> (None, None, permissionSum, permissionSumExp))
    val s1 = s.copy(ssCache = ssc1)

    (s1, permissionSum, permissionSumExp)
  }

  private def summariseOnly(s: State,
                            relevantChunks: Seq[NonQuantifiedChunk],
                            resource: ast.Resource,
                            args: Seq[Term],
                            argsExp: Option[Seq[ast.Exp]],
                            knownValue: Option[Option[Term]],
                            v: Verifier)
                           : (State, TaggedSummarisingSnapshot, Seq[Term], Term, Option[ast.Exp]) = {

    // TODO: Since relevantChunks is a sequence, the order of the chunks affects caching, but shouldn't.
    //       An order-agnostic way of caching, would be better. A simple benchmark should reveal how
    //       many cache misses are due to order changes.

    // TODO: Caching would be more effective if the summary were created independently of the provided
    //       args. E.g. the summary could be created with free arguments ?a1, ?a2, ...; this summary
    //       could be cached, and ?a1 etc. would be replaced before returning the summary to the caller.

    Verifier.config.mapCache(s.ssCache.get((resource, relevantChunks, args))) match {
      case Some((Some(_taggedSummarisingSnapshot), Some(_summarisingSnapshotDefinitions), _permissionSum, _permissionSumExp)) =>
        return (s, _taggedSummarisingSnapshot, _summarisingSnapshotDefinitions, _permissionSum, _permissionSumExp)
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

    relevantChunks.foreach(ch => {
      val argumentEqualities =
        And(ch.args.zip(args).map { case (t1, t2) => t1 === t2 })

      summarisingSnapshotDefinitions :+=
        Implies(And(argumentEqualities, IsPositive(ch.perm)), `?s` === ch.snap)
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
                  val ss = v.decider.appliedFresh("ss", sort, s.functionRecorderQuantifiedVariables().map(_._1) ++ s.quantifiedVariables.map(_._1))
                  FreshSummarisingSnapshot(ss)
              }
          }
        })

    val summarisingSnapshot = taggedSummarisingSnapshot.snapshot

    summarisingSnapshotDefinitions =
      summarisingSnapshotDefinitions map (_.replace(`?s`, summarisingSnapshot))

    val (_, permissionSum, permissionSumExp) = permSummariseOnly(s, relevantChunks, resource, args, argsExp)

    val ssc1 = s.ssCache + ((resource, relevantChunks, args) -> (Some(taggedSummarisingSnapshot), Some(summarisingSnapshotDefinitions), permissionSum, permissionSumExp))
    val s1 = s.copy(ssCache = ssc1)

    (s1, taggedSummarisingSnapshot, summarisingSnapshotDefinitions, permissionSum, permissionSumExp)
  }

  private def summarise(s: State,
                        relevantChunks: Seq[NonQuantifiedChunk],
                        resource: ast.Resource,
                        args: Seq[Term],
                        argsExp: Option[Seq[ast.Exp]],
                        knownValue: Option[Option[Term]], // None if we have not yet checked for a definite alias,
                                                          // Some(v) if we have checked and the result was v
                        v: Verifier)
                       (Q: (State, Term, Term, Option[ast.Exp], Verifier) => VerificationResult)
                       : VerificationResult = {
    // Don't use the shortcut if we want a counterexample; in that case, we need the decider to perform a single
    // query to check if the permission amount we have is sufficient to get the correct counterexample. If we perform
    // the query in two parts (one part here, one part in our caller to see if the permission amount is sufficient),
    // the counterexample might be wrong.
    if (relevantChunks.size == 1 &&  !Verifier.config.counterexample.isDefined) {
      val chunk = relevantChunks.head
      val argsEqual = And(chunk.args.zip(args).map { case (t1, t2) => t1 === t2 })
      if (v.decider.check(argsEqual, Verifier.config.checkTimeout())) {
        return Q(s, chunk.snap, chunk.perm, chunk.permExp, v)
      }
    }

    val (s1, taggedSnap, snapDefs, permSum, permSumExp) = summariseOnly(s, relevantChunks, resource, args, argsExp, knownValue, v)
    v.decider.assumeDefinition(And(snapDefs), Option.when(withExp)(DebugExp.createInstance("Snapshot", true)))
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

    Q(s2, taggedSnap.snapshot, permSum, permSumExp, v)
  }

  def lookupComplete(s: State,
                     h: Heap,
                     resource: ast.Resource,
                     args: Seq[Term],
                     argsExp: Option[Seq[ast.Exp]],
                     ve: VerificationError,
                     v: Verifier)
                    (Q: (State, Term, Verifier) => VerificationResult)
                    : VerificationResult = {

    val id = ChunkIdentifier(resource, s.program)
    val relevantChunks = findChunksWithID[NonQuantifiedChunk](h.values, id).toSeq

    if (relevantChunks.isEmpty) {
      if (v.decider.checkSmoke(true)) {
        if (s.isInPackage) {
          val snap = v.decider.fresh(v.snapshotSupporter.optimalSnapshotSort(resource, s, v), Option.when(withExp)(PUnknown()))
          Q(s, snap, v)
        } else {
          Success() // TODO: Mark branch as dead?
        }
      } else {
        createFailure(ve, v, s, False, "branch is dead")
      }
    } else {
      summarise(s, relevantChunks, resource, args, argsExp, None, v)((s1, snap, permSum, permSumExp, v1) =>
        v.decider.assert(IsPositive(permSum)) {
          case true =>
            Q(s1, snap, v1)
          case false =>
            createFailure(ve, v, s1, IsPositive(permSum), permSumExp.map(IsPositive(_)()))
        })
    }
  }

  def consumeComplete(s: State,
                      h: Heap,
                      resource: ast.Resource,
                      args: Seq[Term],
                      argsExp: Option[Seq[ast.Exp]],
                      perms: Term,
                      permsExp: Option[ast.Exp],
                      returnSnap: Boolean,
                      ve: VerificationError,
                      v: Verifier)
                     (Q: (State, Heap, Option[Term], Verifier) => VerificationResult)
                     : VerificationResult = {

    if (!s.assertReadAccessOnly)
      actualConsumeComplete(s, h, resource, args, argsExp, perms, permsExp, returnSnap, ve, v)(Q)
    else
      summariseHeapAndAssertReadAccess(s, h, resource, perms, args, argsExp, returnSnap, ve, v)(Q)
  }

  private def summariseHeapAndAssertReadAccess(s: State,
                                               h: Heap,
                                               resource: ast.Resource,
                                               perm: Term,
                                               args: Seq[Term],
                                               argsExp: Option[Seq[ast.Exp]],
                                               returnSnap: Boolean,
                                               ve: VerificationError,
                                               v: Verifier)
                                              (Q: (State, Heap, Option[Term], Verifier) => VerificationResult)
                                              : VerificationResult = {

    val id = ChunkIdentifier(resource, s.program)
    val relevantChunks = findChunksWithID[NonQuantifiedChunk](h.values, id).toSeq

    if (returnSnap) {
      summarise(s, relevantChunks, resource, args, argsExp, None, v)((s1, snap, permSum, permSumExp, v1) =>
        v.decider.assert(Implies(IsPositive(perm), IsPositive(permSum))) {
          case true =>
            Q(s1, h, Some(snap), v1)
          case false =>
            createFailure(ve, v, s1, IsPositive(permSum), permSumExp.map(IsPositive(_)()))
        })
    } else {
      val (s1, permSum, permSumExp) = permSummariseOnly(s, relevantChunks, resource, args, argsExp)
      v.decider.assert(Implies(IsPositive(perm), IsPositive(permSum))) {
        case true =>
          Q(s1, h, None, v)
        case false =>
          createFailure(ve, v, s1, IsPositive(permSum), permSumExp.map(IsPositive(_)()))
      }
    }
  }

  private def actualConsumeComplete(s: State,
                                    h: Heap,
                                    resource: ast.Resource,
                                    args: Seq[Term],
                                    argsExp: Option[Seq[ast.Exp]],
                                    perms: Term,
                                    permsExp: Option[ast.Exp],
                                    returnSnap: Boolean,
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
        case false => createFailure(ve, v, s, perms === NoPerm, permsExp.map(pe => ast.EqCmp(pe, ast.NoPerm()())(pe.pos, pe.info, pe.errT)))
      }
    } else {
      if (!terms.utils.consumeExactRead(perms, s.constrainableARPs)) {
        actualConsumeCompleteConstrainable(s, relevantChunks, resource, args, argsExp, perms, permsExp, returnSnap, ve, v)((s1, updatedChunks, optSnap, v2) => {
          Q(s1, Heap(updatedChunks ++ otherChunks), optSnap, v2)
        })
      } else {
        var pNeeded = perms
        var pNeededExp = permsExp
        var pSum: Term = NoPerm
        var pSumExp: Option[ast.Exp] = permsExp.map(pe => ast.NoPerm()(pe.pos, pe.info, pe.errT))
        val newChunks = ListBuffer[NonQuantifiedChunk]()
        var moreNeeded = true

        val definiteAlias = chunkSupporter.findChunk[NonQuantifiedChunk](relevantChunks, id, args, v).filter(c =>
          v.decider.check(IsPositive(c.perm), Verifier.config.checkTimeout())
        )

        val sortFunction: (NonQuantifiedChunk, NonQuantifiedChunk) => Boolean = (ch1, ch2) => {
          // The definitive alias and syntactic aliases should get priority, since it is always
          // possible to consume from them
          definiteAlias.contains(ch1) || !definiteAlias.contains(ch2) && ch1.args == args
        }

        val additionalArgs = s.relevantQuantifiedVariables.map(_._1)
        var currentFunctionRecorder = s.functionRecorder

        relevantChunks.sortWith(sortFunction) foreach { ch =>
          if (moreNeeded) {
            val eqHelper = ch.args.zip(args).map { case (t1, t2) => t1 === t2 }
            val eq = And(eqHelper)
            val eqExp = ch.argsExp.map(args => BigAnd(removeKnownToBeTrueExp(args.zip(argsExp.get).map { case (t1, t2) => ast.EqCmp(t1, t2)(permsExp.get.pos, permsExp.get.info, permsExp.get.errT) }.toList, eqHelper.toList)))

            val takenTerm = Ite(eq, PermMin(ch.perm, pNeeded), NoPerm)
            val pTakenExp = permsExp.map(pe => ast.CondExp(eqExp.get, buildMinExp(Seq(ch.permExp.get, pNeededExp.get), ast.Perm), ast.NoPerm()(pe.pos, pe.info, pe.errT))(eqExp.get.pos, eqExp.get.info, eqExp.get.errT))
            val pTaken = if (takenTerm.isInstanceOf[PermLiteral] || s.functionRecorder != NoopFunctionRecorder || Verifier.config.useFlyweight) {
              // ME: When using Z3 via API, it is beneficial to not use macros, since macro-terms will *always* be different
              // (leading to new terms that have to be translated), whereas without macros, we can usually use a term
              // that already exists.
              // During function verification, we should not define macros, since they could contain result, which is not
              // defined elsewhere.
              // Also, we don't introduce a macro if the term is a straightforward literal.
              takenTerm
            } else {
              val pTakenArgs = additionalArgs
              val pTakenDecl = v.decider.freshMacro("mce_pTaken", pTakenArgs, takenTerm)
              val pTakenMacro = Macro(pTakenDecl.id, pTakenDecl.args.map(_.sort), pTakenDecl.body.sort)
              currentFunctionRecorder = currentFunctionRecorder.recordFreshMacro(pTakenDecl)
              val pTakenApp = App(pTakenMacro, pTakenArgs)
              v.symbExLog.addMacro(pTakenApp, takenTerm)
              pTakenApp
            }

            pSum = PermPlus(pSum, Ite(eq, ch.perm, NoPerm))
            pSumExp = eqExp.map(eq => ast.PermAdd(pSumExp.get, ast.CondExp(eq, ch.permExp.get, ast.NoPerm()())(eq.pos, eq.info, eq.errT))())

            val newChunk = ch.withPerm(PermMinus(ch.perm, pTaken), permsExp.map(pe => ast.PermSub(ch.permExp.get, pTakenExp.get)(pe.pos, pe.info, pe.errT)))
            pNeeded = PermMinus(pNeeded, pTaken)
            pNeededExp = permsExp.map(pe => ast.PermSub(pNeededExp.get, pTakenExp.get)(pe.pos, pe.info, pe.errT))

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
          val pathCond = interpreter.buildPathConditionsForChunk(ch, resource.instanceProperties(s.mayAssumeUpperBounds))
          pathCond.foreach(p => v.decider.assume(p._1, Option.when(withExp)(DebugExp.createInstance(p._2, p._2))))
        }
        val newHeap = Heap(allChunks)

        val s0 = s.copy(functionRecorder = currentFunctionRecorder)



        if (returnSnap) {
          summarise(s0, relevantChunks.toSeq, resource, args, argsExp, Some(definiteAlias.map(_.snap)), v)((s1, snap, _, _, v1) => {
            val condSnap = Some(if (v1.decider.check(IsPositive(perms), Verifier.config.checkTimeout())) {
              snap
            } else {
              Ite(IsPositive(perms), snap.convert(sorts.Snap), Unit)
            })
          if (!moreNeeded) {
            Q(s1, newHeap, condSnap, v1)
          } else {
            v1.decider.assert(pNeeded === NoPerm) {
              case true =>
                Q(s1, newHeap, condSnap, v1)
              case false =>
                createFailure(ve, v1, s1, pNeeded === NoPerm, pNeededExp.map(pn => ast.EqCmp(pn, ast.NoPerm()())(pn.pos, pn.info, pn.errT)))
            }
          }
        })
        } else {
          if (!moreNeeded) {
            Q(s0, newHeap, None, v)
          } else {
            v.decider.assert(pNeeded === NoPerm) {
              case true =>
                Q(s0, newHeap, None, v)
              case false =>
                createFailure(ve, v, s0, pNeeded === NoPerm, pNeededExp.map(pn => ast.EqCmp(pn, ast.NoPerm()())(pn.pos, pn.info, pn.errT)))
            }
          }
        }
      }
    }
  }

  private def actualConsumeCompleteConstrainable(s: State,
                                                 relevantChunks: ListBuffer[NonQuantifiedChunk],
                                                 resource: ast.Resource,
                                                 args: Seq[Term],
                                                 argsExp: Option[Seq[ast.Exp]],
                                                 perms: Term, // Expected to be constrainable. Will be assumed to equal the consumed permission amount.
                                                 permsExp: Option[ast.Exp],
                                                 returnSnap: Boolean,
                                                 ve: VerificationError,
                                                 v: Verifier)
                                                (Q: (State, ListBuffer[NonQuantifiedChunk], Option[Term], Verifier) => VerificationResult)
                                                : VerificationResult = {

    v.decider.startDebugSubExp()

    var totalPermSum: Term = NoPerm
    var totalPermSumExp: Option[ast.Exp] = Option.when(withExp)(ast.NoPerm()())
    var totalPermTaken: Term = NoPerm
    var totalPermTakenExp: Option[ast.Exp] = Option.when(withExp)(ast.NoPerm()())
    var newFr = s.functionRecorder


    val updatedChunks =
      relevantChunks map (ch => {
        val eqCmps = ch.args.zip(args).map { case (t1, t2) => t1 === t2 }
        val eq = And(eqCmps)
        val eqExp = permsExp.map(pe => BigAnd(removeKnownToBeTrueExp(ch.argsExp.get.zip(argsExp.get).map{ case (t1, t2) => ast.EqCmp(t1, t2)(pe.pos, pe.info, pe.errT) }.toList, eqCmps.toList)))
        val permTaken = v.decider.appliedFresh("p", sorts.Perm, s.functionRecorderQuantifiedVariables().map(_._1) ++ s.quantifiedVariables.map(_._1))
        val permTakenExp = permsExp.map(pe => ast.LocalVar(simplifyVariableName(permTaken.applicable.id.name), ast.Perm)(pe.pos, pe.info, pe.errT))

        totalPermSum = PermPlus(totalPermSum, Ite(eq, ch.perm, NoPerm))
        totalPermSumExp = totalPermSumExp.map(tps => ast.PermAdd(tps, ast.CondExp(eqExp.get, ch.permExp.get, ast.NoPerm()())(eqExp.get.pos, eqExp.get.info, eqExp.get.errT))(permsExp.get.pos, permsExp.get.info, permsExp.get.errT))
        totalPermTaken = PermPlus(totalPermTaken, permTaken)
        totalPermTakenExp = totalPermTakenExp.map(tpt => ast.PermAdd(tpt, permTakenExp.get)(permsExp.get.pos, permsExp.get.info, permsExp.get.errT))

        val constraint = And(IsValidPermVal(permTaken),
          PermAtMost(permTaken, ch.perm),
          Implies(Not(eq), permTaken === NoPerm),
          Implies(And(eq, IsPositive(ch.perm)), PermLess(permTaken, ch.perm))
        )
        val constraintExp = permsExp.map(pe => BigAnd(
          List(ast.PermLtCmp(ast.NoPerm()(), permTakenExp.get)(),
            ast.PermLeCmp(permTakenExp.get, ch.permExp.get)(),
            ast.Implies(ast.Not(eqExp.get)(), ast.EqCmp(permTakenExp.get, ast.NoPerm()())())(pe.pos, pe.info, pe.errT))))


        v.decider.assume(constraint, Option.when(withExp)(DebugExp.createInstance(constraintExp, constraintExp)))

        newFr = newFr.recordPathSymbol(permTaken.applicable.asInstanceOf[Function]).recordConstraint(constraint)

        ch.withPerm(PermMinus(ch.perm, permTaken), permsExp.map(pe => ast.PermSub(ch.permExp.get, permTakenExp.get)(pe.pos, pe.info, pe.errT)))
      })

    val totalTakenBounds =
      Implies(
        totalPermSum !== NoPerm,
        And(
          PermLess(NoPerm, totalPermTaken),
          PermLess(totalPermTaken, totalPermSum)))
    val constraintExp = permsExp.map(pe => ast.Implies(ast.NeCmp(totalPermSumExp.get, ast.NoPerm()())(),
      ast.And(ast.PermLeCmp(ast.NoPerm()(), totalPermTakenExp.get)(), ast.PermLeCmp(totalPermTakenExp.get, totalPermSumExp.get)())(pe.pos, pe.info, pe.errT))())

    v.decider.assume(totalTakenBounds, constraintExp, constraintExp)

    newFr = newFr.recordConstraint(totalTakenBounds)

    val s1 = s.copy(functionRecorder = newFr)

    v.decider.assert(Implies(PermLess(NoPerm, perms), totalPermTaken !== NoPerm)) {
      case true =>
        val constraintExp = permsExp.map(pe => ast.EqCmp(pe, totalPermTakenExp.get)())
        v.decider.assume(perms === totalPermTaken, Option.when(withExp)(DebugExp.createInstance(constraintExp, constraintExp)))
        if (returnSnap) {
          summarise(s1, relevantChunks.toSeq, resource, args, argsExp, None, v)((s2, snap, _, _, v1) =>
            Q(s2, updatedChunks, Some(snap), v1))
        } else {
          Q(s1, updatedChunks, None, v)
        }
      case false =>
        v.decider.finishDebugSubExp(s"consume permissions for ${resource.toString()}")
        createFailure(ve, v, s, totalPermTaken !== NoPerm, totalPermTakenExp.map(tpt => ast.NeCmp(tpt, ast.NoPerm()())()))
    }
  }

  private val freeReceiver = Var(Identifier("?rcvr"), sorts.Ref, false)
  private val freeReceiverExp = ast.LocalVar("?rcvr", ast.Ref)()

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
      val permissionSumExp = Option.when(withExp)(relevantChunks.foldLeft(ast.NoPerm()(): ast.Exp) { case (permSumExp, chunk) =>
        val eq = ast.EqCmp(freeReceiverExp, chunk.argsExp.get.head)() /* For field chunks, the receiver is the only argument */
        ast.PermAdd(permSumExp, ast.CondExp(eq, chunk.permExp.get, ast.NoPerm()())())()
      })

      relevantChunks foreach (chunk => {
        val instantiatedPermSum = permissionSum.replace(freeReceiver, chunk.args.head)
        val exp = permissionSumExp.map(pse => ast.PermLeCmp(replaceVarsInExp(pse, Seq(freeReceiverExp.name), Seq(chunk.argsExp.get.head)), ast.FullPerm()())())
        v.decider.assume(PermAtMost(instantiatedPermSum, FullPerm), exp, exp)
      })
    }
  }
}
