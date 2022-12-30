// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2022 ETH Zurich.

package viper.silicon.rules

import viper.silicon.interfaces.VerificationResult
import viper.silicon.interfaces.state.CarbonChunk
import viper.silicon.rules.quantifiedChunkSupporter.{createFailure, getFreshInverseFunctions}
import viper.silicon.state.terms.perms.IsPositive
import viper.silicon.state.terms.sorts.{MaskSort, PredMaskSort}
import viper.silicon.state.terms.{And, AtLeast, FakeMaskMapTerm, Forall, FullPerm, Greater, HeapLookup, HeapSingleton, HeapUpdate, IdenticalOnKnownLocations, Implies, Ite, MaskAdd, MaskDiff, MaskSum, MergeHeaps, MergeSingle, NoPerm, Null, PermAtMost, PermLess, PermMinus, PermNegation, PermPlus, PermTimes, Quantification, Term, Trigger, True, Var, perms, sorts, toSnapTree}
import viper.silicon.state.{BasicCarbonChunk, ChunkIdentifier, FunctionPreconditionTransformer, Heap, State, terms}
import viper.silicon.supporters.functions.NoopFunctionRecorder
import viper.silicon.verifier.Verifier
import viper.silver.verifier.{ErrorReason, PartialVerificationError}
import viper.silver.ast
import viper.silver.ast.PermAdd
import viper.silver.reporter.InternalWarningMessage
import viper.silver.verifier.reasons.{InsufficientPermission, MagicWandChunkNotFound}

class CarbonQuantifiedChunkSupport extends SymbolicExecutionRules {

}

object carbonQuantifiedChunkSupporter extends CarbonQuantifiedChunkSupport {

  def findCarbonChunk(h: Heap, r: ast.Resource) = h.values.find(c => c.asInstanceOf[CarbonChunk].resource == r).get.asInstanceOf[BasicCarbonChunk]

  def consumeSingleLocation(s: State,
                            h: Heap,
                            codomainQVars: Seq[Var], /* rs := r_1, ..., r_m */
                            arguments: Seq[Term], // es := e_1, ..., e_n
                            resourceAccess: ast.ResourceAccess,
                            permissions: Term, /* p */
                            pve: PartialVerificationError,
                            v: Verifier,
                            resMap: Map[ast.Resource, Term])
                           (Q: (State, Heap, Term, Verifier) => VerificationResult)
  : VerificationResult = {
    val resource = resourceAccess.res(s.program)

    // assert enough
    // TODO: create failures only when needed? This can lead to CE extraction, which is expensive.
    val failure = resourceAccess match {
      case locAcc: ast.LocationAccess => createFailure(pve dueTo InsufficientPermission(locAcc), v, s)
      case wand: ast.MagicWand => createFailure(pve dueTo MagicWandChunkNotFound(wand), v, s)
      case _ => sys.error(s"Found resource $resourceAccess, which is not yet supported as a quantified resource.")
    }

    if (s.exhaleExt) {
      ???
    } else {
      val resChunk = findCarbonChunk(h, resource)

      val argTerm = resource match {
        case _: ast.Field => arguments(0)
        case _: ast.Predicate => toSnapTree(arguments)
      }

      val consumeExact = terms.utils.consumeExactRead(permissions, s.constrainableARPs)

      val maskValue = HeapLookup(resChunk.mask, argTerm)

      val toCheck = if (consumeExact) AtLeast(maskValue, permissions) else Greater(maskValue, NoPerm())

      v.decider.assert(toCheck) {
        case true =>
          if (!consumeExact) {
            // constrain wildcard
            v.decider.assume(PermLess(permissions, maskValue))
          }
          val newMask = MaskAdd(resChunk.mask, argTerm, PermNegation(permissions))//HeapUpdate(resChunk.mask, argTerm, PermMinus(maskValue, permissions))
          val newChunk = if (s.functionRecorder != NoopFunctionRecorder) {
            // no need to havoc
            resChunk.copy(mask = newMask)
          } else {
            val freshHeap = v.decider.fresh("heap", resChunk.heap.sort)
            v.decider.assume(IdenticalOnKnownLocations(resChunk.heap, freshHeap, newMask))
            resChunk.copy(mask = newMask, heap = freshHeap)
          }

          //val snap = HeapLookup(resChunk.heap, argTerm).convert(sorts.Snap)
          val newSnapMask = MaskAdd(resMap(resource), argTerm, permissions) //HeapUpdate(resMap(resource), argTerm, PermPlus(HeapLookup(resMap(resource), argTerm), permissions))
          val snap = FakeMaskMapTerm(resMap.updated(resource, newSnapMask))
          // set up partially consumed heap
          Q(s, h - resChunk + newChunk, snap, v)
        case false => failure
      }
    }
  }

  def consume(s: State,
              h: Heap,
              resource: ast.Resource,
              qvars: Seq[Var],
              formalQVars: Seq[Var],
              qid: String,
              optTrigger: Option[Seq[ast.Trigger]],
              tTriggers: Seq[Trigger],
              auxGlobals: Seq[Term],
              auxNonGlobals: Seq[Quantification],
              tCond: Term,
              tArgs: Seq[Term],
              tPerm: Term,
              pve: PartialVerificationError,
              negativePermissionReason: => ErrorReason,
              notInjectiveReason: => ErrorReason,
              insufficientPermissionReason: => ErrorReason,
              v: Verifier,
              resMap: Map[ast.Resource, Term])
             (Q: (State, Heap, Term, Verifier) => VerificationResult)
  : VerificationResult = {

    val (inverseFunctions, imagesOfFormalQVars) =
      quantifiedChunkSupporter.getFreshInverseFunctions(
        qvars,
        And(tCond, IsPositive(tPerm)),
        tArgs,
        formalQVars,
        s.relevantQuantifiedVariables(tArgs),
        optTrigger.map(_ => tTriggers),
        qid,
        v)
    val (effectiveTriggers, effectiveTriggersQVars) =
      optTrigger match {
        case Some(_) =>
          /* Explicit triggers were provided */
          (tTriggers, qvars)
        case None =>
          /* No explicit triggers were provided and we resort to those from the inverse
            * function axiom inv-of-rcvr, i.e. from `inv(e(x)) = x`.
            * Note that the trigger generation code might have added quantified variables
            * to that axiom.
            */
          (inverseFunctions.axiomInversesOfInvertibles.triggers,
            inverseFunctions.axiomInversesOfInvertibles.vars)
      }
    v.decider.prover.comment("Nested auxiliary terms: globals")
    v.decider.assume(auxGlobals)
    v.decider.prover.comment("Nested auxiliary terms: non-globals")
    optTrigger match {
      case None =>
        /* No explicit triggers provided */
        v.decider.assume(
          auxNonGlobals.map(_.copy(
            vars = effectiveTriggersQVars,
            triggers = effectiveTriggers)))
      case Some(_) =>
        /* Explicit triggers were provided. */
        v.decider.assume(auxNonGlobals)
    }

    val nonNegImplication = Implies(tCond, perms.IsNonNegative(tPerm))
    val nonNegTerm = Forall(qvars, Implies(FunctionPreconditionTransformer.transform(nonNegImplication, s.program), nonNegImplication), Nil)
    // TODO: Replace by QP-analogue of permissionSupporter.assertNotNegative
    v.decider.assert(nonNegTerm) {
      case true =>
        val loss = PermTimes(tPerm, s.permissionScalingFactor)

        /* TODO: Can we omit/simplify the injectivity check in certain situations? */
        val receiverInjectivityCheck =
          quantifiedChunkSupporter.injectivityAxiom(
            qvars     = qvars,
            condition = tCond,
            perms     = tPerm,
            arguments = tArgs,
            triggers  = Nil,
            qidPrefix = qid,
            program = s.program)
        v.decider.prover.comment("Check receiver injectivity")
        v.decider.assert(receiverInjectivityCheck) {
          case true =>
            val qvarsToInvOfLoc = inverseFunctions.qvarsToInversesOf(formalQVars)
            val condOfInvOfLoc = tCond.replace(qvarsToInvOfLoc)
            val lossOfInvOfLoc = loss.replace(qvarsToInvOfLoc)

            v.decider.prover.comment("Definitional axioms for inverse functions")
            v.decider.assume(inverseFunctions.definitionalAxioms.map(a => FunctionPreconditionTransformer.transform(a, s.program)))
            v.decider.assume(inverseFunctions.definitionalAxioms)

            /*
            if (s.heapDependentTriggers.contains(resourceIdentifier)){
              v.decider.assume(
                Forall(
                  formalQVars,
                  Implies(condOfInvOfLoc, ResourceTriggerFunction(resource, smDef1.get.sm, formalQVars, s.program)),
                  Trigger(inverseFunctions.inversesOf(formalQVars))))
            }
             */

            /* TODO: Try to unify the upcoming if/else-block, their code is rather similar */
            if (s.exhaleExt) {
              ???
            } else {
              val currentChunk = findCarbonChunk(h, resource)
              val argTerm = resource match {
                case _: ast.Field => formalQVars(0)
                case _: ast.Predicate => toSnapTree(formalQVars)
              }
              // assert enough permissions
              val currentPerm = HeapLookup(currentChunk.mask, argTerm)
              v.decider.assert(Forall(formalQVars, Implies(condOfInvOfLoc, PermAtMost(lossOfInvOfLoc, currentPerm)), Seq(), "sufficientPerms"))(r => r match {
              case true =>
                // remove permissions
                val qpMask = v.decider.fresh("heap", if (resource.isInstanceOf[ast.Field]) MaskSort else PredMaskSort)
                val qpMaskGet = HeapLookup(qpMask, argTerm)
                val conditionalizedPermissions = Ite(condOfInvOfLoc, lossOfInvOfLoc, NoPerm())
                val qpMaskConstraint = Forall(formalQVars, qpMaskGet === conditionalizedPermissions, Seq(Trigger(qpMaskGet)), "qpMaskdef")
                v.decider.assume(qpMaskConstraint)
                val newMask = MaskDiff(currentChunk.mask, qpMask)
                val newChunk = currentChunk.copy(mask = newMask)
                // create snap

                // continue
                val newFr = s.functionRecorder.recordFieldInv (inverseFunctions).recordArp(qpMask, qpMaskConstraint)
                val newHeap = h - currentChunk + newChunk
                val s2 = s.copy(functionRecorder = newFr, partiallyConsumedHeap = Some(newHeap))
                val newSnapMask = MaskSum(resMap(resource), qpMask)
                val snap = FakeMaskMapTerm(resMap.updated(resource, newSnapMask))
                Q(s2, newHeap, snap, v)
              case false =>
                createFailure (pve dueTo insufficientPermissionReason, v, s)
              })
            }
          case false =>
            createFailure(pve dueTo notInjectiveReason, v, s)}
      case false =>
        createFailure(pve dueTo negativePermissionReason, v, s)}
  }

  def produceSingleLocation(s: State,
                            resource: ast.Resource,
                            tArgs: Seq[Term],
                            tPerm: Term,
                            v: Verifier,
                            snap: Term)
                           (Q: (State, Verifier) => VerificationResult)
  : VerificationResult = {

    val resChunk = s.h.values.find(c => c.asInstanceOf[CarbonChunk].resource == resource).get.asInstanceOf[BasicCarbonChunk]
    val argTerm = resource match {
      case _: ast.Field => tArgs(0)
      case _: ast.Predicate => toSnapTree(tArgs)
    }
    val newMask = MaskAdd(resChunk.mask, argTerm, tPerm) // HeapUpdate(resChunk.mask, argTerm, PermPlus(HeapLookup(resChunk.mask, argTerm), tPerm))
    val snapHeapMap = snap.asInstanceOf[FakeMaskMapTerm].masks

    val newHeap = MergeSingle(resChunk.heap, resChunk.mask, argTerm, HeapLookup(snapHeapMap(resource), argTerm))
    val ch = resChunk.copy(mask = newMask, heap = newHeap)
    val h1 = s.h - resChunk + ch

    val permConstraint = if (resource.isInstanceOf[ast.Field])
      And(Implies(perms.IsPositive(tPerm), argTerm !== Null()), PermAtMost(HeapLookup(ch.mask, argTerm), FullPerm()))
    else True()
    v.decider.assume(permConstraint)
    
    val s1 = s.copy(h = h1)
    Q(s1, v)
  }

  def produce(s: State,
              forall: ast.Forall,
              resource: ast.Resource,
              qvars: Seq[Var],
              formalQVars: Seq[Var],
              qid: String,
              optTrigger: Option[Seq[ast.Trigger]],
              tTriggers: Seq[Trigger],
              auxGlobals: Seq[Term],
              auxNonGlobals: Seq[Quantification],
              tCond: Term,
              tArgs: Seq[Term],
              tSnap: Term,
              tPerm: Term,
              pve: PartialVerificationError,
              negativePermissionReason: => ErrorReason,
              notInjectiveReason: => ErrorReason,
              v: Verifier)
             (Q: (State, Verifier) => VerificationResult)
  : VerificationResult = {

    val gain = PermTimes(tPerm, s.permissionScalingFactor)
    /*
    val (ch: QuantifiedBasicChunk, inverseFunctions) =
      quantifiedChunkSupporter.createQuantifiedChunk(
        qvars                = qvars,
        condition            = tCond,
        resource             = resource,
        arguments            = tArgs,
        permissions          = gain,
        codomainQVars        = formalQVars,
        sm                   = tSnap,
        additionalInvArgs    = s.relevantQuantifiedVariables(tArgs),
        userProvidedTriggers = optTrigger.map(_ => tTriggers),
        qidPrefix            = qid,
        v                    = v,
        program              = s.program)

     */

    val (inverseFunctions, imagesOfCodomain) =
      getFreshInverseFunctions(
        qvars,
        And(tCond, IsPositive(gain)),
        tArgs,
        formalQVars,
        s.relevantQuantifiedVariables(tArgs),
        optTrigger.map(_ => tTriggers),
        qid,
        v)

    val qvarsToInversesOfCodomain = inverseFunctions.qvarsToInversesOf(formalQVars)

    val conditionalizedPermissions =
      Ite(
        And(And(imagesOfCodomain), tCond.replace(qvarsToInversesOfCodomain)),
        gain.replace(qvarsToInversesOfCodomain),
        NoPerm())

    val qpMask = v.decider.fresh("heap", if (resource.isInstanceOf[ast.Field]) MaskSort else PredMaskSort)
    // forall r :: { get(qpMask, r) } get(qpMask, r) == conditionalizedPermissions
    val argTerm = resource match {
      case _: ast.Field => formalQVars(0)
      case _: ast.Predicate => toSnapTree(formalQVars)
    }
    val qpMaskGet = HeapLookup(qpMask, argTerm)
    val qpMaskConstraint = Forall(formalQVars, qpMaskGet === conditionalizedPermissions, Seq(Trigger(qpMaskGet)), "qpMaskdef")
    v.decider.assume(qpMaskConstraint)

    val currentChunk = findCarbonChunk(s.h, resource)
    val newMask =  MaskSum(currentChunk.mask, qpMask)
    val snapHeapMap = tSnap.asInstanceOf[FakeMaskMapTerm].masks
    val newHeap = MergeHeaps(currentChunk.heap, currentChunk.mask, snapHeapMap(resource), qpMask)
    val newChunk = currentChunk.copy(mask = newMask, heap = newHeap)
    val newMaskGet = HeapLookup(newMask, argTerm)


    val permBoundConstraint = resource match {
      case _: ast.Field => And(Forall(formalQVars, PermAtMost(newMaskGet, FullPerm()), Seq(Trigger(newMaskGet)), "qp_produce_upper_bound"),
        Forall(formalQVars, Implies(And(And(And(imagesOfCodomain), tCond.replace(qvarsToInversesOfCodomain)), PermLess(NoPerm(), gain.replace(qvarsToInversesOfCodomain))), formalQVars(0) !== Null()), Seq(), "qp_recvr_non_null"))
      case _ => True()
    }

    val (effectiveTriggers, effectiveTriggersQVars) =
      optTrigger match {
        case Some(_) =>
          (tTriggers, qvars)
        case None =>
          /* No explicit triggers were provided and we resort to those from the inverse
           * function axiom inv-of-rcvr, i.e. from `inv(e(x)) = x`.
           * Note that the trigger generation code might have added quantified variables
           * to that axiom.
           */
          (inverseFunctions.axiomInversesOfInvertibles.triggers,
            inverseFunctions.axiomInversesOfInvertibles.vars)
      }

    if (effectiveTriggers.isEmpty) {
      val msg = s"No triggers available for quantifier at ${forall.pos}"
      v.reporter report InternalWarningMessage(msg)
      v.logger warn msg
    }

    v.decider.prover.comment("Nested auxiliary terms: globals")
    v.decider.assume(auxGlobals)
    v.decider.prover.comment("Nested auxiliary terms: non-globals")
    v.decider.assume(
      auxNonGlobals.map(_.copy(
        vars = effectiveTriggersQVars,
        triggers = effectiveTriggers)))

    val nonNegImplication = Implies(tCond, perms.IsNonNegative(tPerm))
    val nonNegTerm = Forall(qvars, Implies(FunctionPreconditionTransformer.transform(nonNegImplication, s.program), nonNegImplication), Nil)
    // TODO: Replace by QP-analogue of permissionSupporter.assertNotNegative
    v.decider.assert(nonNegTerm) {
      case true =>

        /* TODO: Can we omit/simplify the injectivity check in certain situations? */
        val receiverInjectivityCheck =
          if (!Verifier.config.assumeInjectivityOnInhale()) {
            quantifiedChunkSupporter.injectivityAxiom(
              qvars     = qvars,
              // TODO: Adding ResourceTriggerFunction requires a summarising snapshot map of the current heap
              condition = tCond, // And(tCond, ResourceTriggerFunction(resource, smDef1.sm, tArgs)),
              perms     = tPerm,
              arguments = tArgs,
              triggers  = Nil,
              qidPrefix = qid,
              program   = s.program)
          } else {
            True()
          }
        v.decider.prover.comment("Check receiver injectivity")
        v.decider.assume(FunctionPreconditionTransformer.transform(receiverInjectivityCheck, s.program))
        v.decider.assert(receiverInjectivityCheck) {
          case true =>
            val ax = inverseFunctions.axiomInversesOfInvertibles
            val inv = inverseFunctions.copy(axiomInversesOfInvertibles = Forall(ax.vars, ax.body, effectiveTriggers))

            v.decider.prover.comment("Definitional axioms for inverse functions")
            val definitionalAxiomMark = v.decider.setPathConditionMark()
            v.decider.assume(inv.definitionalAxioms.map(a => FunctionPreconditionTransformer.transform(a, s.program)))
            v.decider.assume(inv.definitionalAxioms)
            val conservedPcs =
              if (s.recordPcs) (s.conservedPcs.head :+ v.decider.pcs.after(definitionalAxiomMark)) +: s.conservedPcs.tail
              else s.conservedPcs
            /*
            val resourceDescription = Resources.resourceDescriptions(ch.resourceID)
            val interpreter = new QuantifiedPropertyInterpreter
            resourceDescription.instanceProperties.foreach (property => {
              v.decider.prover.comment(property.description)
              v.decider.assume(interpreter.buildPathConditionForChunk(
                chunk = ch,
                property = property,
                qvars = effectiveTriggersQVars,
                args = tArgs,
                perms = gain,
                condition = tCond,
                triggers = effectiveTriggers,
                qidPrefix = qid)
              )
            })

             */

            val h1 = s.h - currentChunk + newChunk
            v.decider.assume(permBoundConstraint)

            val s1 =
              s.copy(h = h1,
                functionRecorder = s.functionRecorder.recordFieldInv(inv).recordArp(qpMask, qpMaskConstraint),
                conservedPcs = conservedPcs)
            Q(s1, v)
          case false =>
            createFailure(pve dueTo notInjectiveReason, v, s)}
      case false =>
        createFailure(pve dueTo negativePermissionReason, v, s)}
  }
}
