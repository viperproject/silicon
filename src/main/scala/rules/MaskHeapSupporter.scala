// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2025 ETH Zurich.

package viper.silicon.rules

import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.debugger.DebugExp
import viper.silicon.decider.Decider
import viper.silicon.interfaces.VerificationResult
import viper.silicon.interfaces.state.MaskHeapChunk
import viper.silicon.resources.MagicWandID
import viper.silicon.state.terms.perms.IsPositive
import viper.silicon.state.terms.sorts.{MaskSort, PredHeapSort, PredMaskSort}
import viper.silicon.state.terms.utils.consumeExactRead
import viper.silicon.state.terms.{And, AtLeast, AtMost, DummyHeap, FakeMaskMapTerm, Forall, FullPerm, GoodFieldMask, GoodMask, Greater, HeapLookup, HeapToSnap, IdenticalOnKnownLocations, Implies, Ite, MaskAdd, MaskDiff, MaskSum, MergeHeaps, MergeSingle, NoPerm, Null, PermAtMost, PermLess, PermMin, PermMinus, PermNegation, PermTimes, PredZeroMask, Quantification, Term, Trigger, True, Var, ZeroMask, perms, sorts, toSnapTree}
import viper.silicon.state.{BasicMaskHeapChunk, FunctionPreconditionTransformer, Heap, Identifier, MagicWandIdentifier, State, terms}
import viper.silicon.supporters.functions.NoopFunctionRecorder
import viper.silicon.verifier.Verifier
import viper.silver.verifier.{ErrorReason, PartialVerificationError}
import viper.silver.ast
import viper.silver.components.StatefulComponent
import viper.silver.parser.PUnknown
import viper.silver.reporter.InternalWarningMessage
import viper.silver.verifier.reasons.{InsufficientPermission, MagicWandChunkNotFound}

import scala.collection.mutable.ListBuffer
import scala.collection.{immutable, mutable}

object maskHeapSupporter extends SymbolicExecutionRules with StatefulComponent {

  val assumeGoodMask = true
  lazy val simplifyOnConsume: Boolean = Verifier.config.simplifyOnConsume()

  val resCache = mutable.HashMap[Seq[ast.Exp], Seq[Any]]()

  override def start(): Unit = { }
  override def stop(): Unit = {}
  override def reset(): Unit = {
    resCache.clear()
  }
  def getResourceSeq(tlcs: Seq[ast.Exp], program: ast.Program): Seq[Any] = {
    val key = tlcs
    val current = resCache.get(key)
    if (current.isDefined)
      return current.get
    val resources = tlcs.map(_.shallowCollect {
      case ast.PredicateAccessPredicate(pa, _) => pa.loc(program)
      case ast.FieldAccessPredicate(fa, _) => fa.loc(program)
      case mw: ast.MagicWand => MagicWandIdentifier(mw, program)
    }).flatten.distinct.sortWith((r1, r2) => {
      val r1Name = r1 match {
        case f: ast.Field => f.name
        case p: ast.Predicate => p.name
        case mwi: MagicWandIdentifier => mwi.toString
      }
      val r2Name = r2 match {
        case f: ast.Field => f.name
        case p: ast.Predicate => p.name
        case mwi: MagicWandIdentifier => mwi.toString
      }
      r1Name < r2Name
    })
    resCache.put(key, resources)
    resources
  }

  def findMaskHeapChunk(h: Heap, r: Any) = findMaskHeapChunkOptionally(h, r).get

  def findMaskHeapChunkOptionally(h: Heap, r: Any) = h.values.find(c => c.asInstanceOf[MaskHeapChunk].resource == r).asInstanceOf[Option[BasicMaskHeapChunk]]

  def findOrCreateMaskHeapChunk(h: Heap, mwi: MagicWandIdentifier, v: Verifier) = {
    h.values.find(c => c.asInstanceOf[MaskHeapChunk].resource == mwi) match {
      case Some(c: BasicMaskHeapChunk) => (h, c)
      case None =>
        val newHeap = v.decider.fresh("mwHeap", PredHeapSort, Option.when(withExp)(PUnknown()))
        val newChunk = BasicMaskHeapChunk(MagicWandID, mwi, PredZeroMask, newHeap)
        (h + newChunk, newChunk)
    }
  }

  def mergeWandHeaps(h: Heap, newH: Heap, v: Verifier, s: Option[State]): Heap = {
    val resources = (h.values.map(c => c.asInstanceOf[BasicMaskHeapChunk].resource) ++
      newH.values.map(c => c.asInstanceOf[BasicMaskHeapChunk].resource)).toSeq.distinct

    val mergedChunks = resources.map(r => {
      val oldChunk = findMaskHeapChunkOptionally(h, r)
      val newChunk = findMaskHeapChunkOptionally(newH, r)
      (oldChunk, newChunk) match {
        case (Some(c1), Some(c2)) =>
          val newMask = MaskSum(c1.mask, c2.mask)
          val newHeap = MergeHeaps(c1.heap, c1.mask, c2.heap, c2.mask)
          if (r.isInstanceOf[ast.Field]) {
            if (newMask != c1.mask && newMask != c2.mask)
              v.decider.assume(upperBoundAssertion(newMask, v), Option.when(withExp)(DebugExp.createInstance("Upper bound assertion for merged field mask")))
          }
          c1.copy(newMask = newMask, newHeap = newHeap)
        case (Some(c1), None) => c1
        case (None, Some(c2)) => c2
      }
    })

    val mergedHeap = Heap(mergedChunks)
    mergedHeap
  }

  def convertToSnapshot(masks: Map[Any, Term], resources: Seq[Any], h: Heap, s: State, d: Decider) = {
    val snapTerms = resources.map(r => {
      val chunk = findMaskHeapChunkOptionally(h, r)
      if (chunk.isEmpty) {
        terms.Unit
      } else if (chunk.get.heap.isInstanceOf[DummyHeap]) {
        terms.Unit
      } else {
        HeapToSnap(chunk.get.heap, masks(r), r)
      }
    })
    toSnapTree(snapTerms)
  }

  def upperBoundAssertion(mask: Term, v: Verifier): Term = {
    val receivers = mutable.LinkedHashSet[Term]()
    val masks = mutable.LinkedHashSet[Term]()

    def traverse(mask: Term): Unit = mask match {
      case MaskAdd(m, r, v) => receivers.add(r); traverse(m)
      case MaskSum(m1, m2) => traverse(m1); traverse(m2)
      case MaskDiff(m1, m2) => masks.add(m2); traverse(m1)
      case ZeroMask =>
      case PredZeroMask =>
      case t => masks.add(t)
    }

    traverse(mask)

    val individualAssumes = And(receivers.map(r => PermAtMost(HeapLookup(mask, r), FullPerm)))
    val qvar = v.decider.fresh(sorts.Ref, Option.when(withExp)(PUnknown()))
    val triggers = (masks ++ Seq(mask)).map(m => Trigger(HeapLookup(m, qvar))).toSeq
    val maskAssume = Forall(qvar, PermAtMost(HeapLookup(mask, qvar), FullPerm), triggers)
    And(individualAssumes, maskAssume)
  }

  def removeSingleAdd(origMask: Term, at: Term, amount: Term, s: State, v: Verifier): Term = {
    if (!simplifyOnConsume) {
      return MaskAdd(origMask, at, PermNegation(amount))
    }

    val termAdditions = mutable.LinkedHashMap[Term, Term]()
    val termRemovals = mutable.LinkedHashMap[Term, Term]()
    val maskAdditions = mutable.LinkedHashSet[Term]()
    val maskRemovals = mutable.LinkedHashSet[Term]()

    var remainingAmount = amount
    var done = false

    def traverse(mask: Term): Unit = mask match {
      case MaskAdd(m, r, PermNegation(v)) => termRemovals.update(r, v); traverse(m)
      case MaskAdd(m, r, v) => termAdditions.update(r, v); traverse(m)
      case MaskSum(m1, m2) => traverse(m1); traverse(m2)
      case MaskDiff(m1, m2) => maskRemovals.add(m2); traverse(m1)
      case ZeroMask =>
      case PredZeroMask =>
      case t => maskAdditions.add(t)
    }
    traverse(origMask)

    val syntacticAdditions = termAdditions.filter(_._1 == at)
    val directMatch = syntacticAdditions.find(_._2 == amount)

    val toReplace = mutable.HashMap.from(if (directMatch.isDefined) {
      remainingAmount = NoPerm
      Seq((directMatch.get, NoPerm))
    } else {
      val additions = (syntacticAdditions ++ termAdditions.filterNot(_._2 == at)).toSeq.distinct
      val result = ListBuffer[((Term, Term), Term)]()
      for ((r, add) <- additions) {
        if (!done) {
          if (v.decider.check(at === r, Verifier.config.checkTimeout())) {
            val toTake = PermMin(add, remainingAmount)
            remainingAmount = PermMinus(remainingAmount, toTake)
            val chunkLeft = PermMinus(add, toTake)
            result.append(((r, add), chunkLeft))

            if (v.decider.check(remainingAmount === NoPerm, Verifier.config.checkTimeout()))
              done = true
          }
        }
      }
      result.toSeq
    })

    if (toReplace.nonEmpty) {
      def replace(mask: Term): Term = mask match {
        case mask if toReplace.isEmpty => mask
        case MaskAdd(m, r, vl) if toReplace.contains((r, vl)) =>
          val newVal = toReplace((r, vl))
          toReplace.remove((r, vl))
          MaskAdd(replace(m), r, newVal)
        case MaskAdd(m, r, v) => MaskAdd(replace(m), r, v)
        case MaskSum(m1, m2) => MaskSum(replace(m1), replace(m2))
        case MaskDiff(m1, m2) => MaskDiff(replace(m1), m2)
        case ZeroMask => mask
        case PredZeroMask => mask
        case t => t
      }
      val replaced = replace(origMask)
      val res = MaskAdd(replaced, at, PermNegation(remainingAmount))
      res
    } else {
      MaskAdd(origMask, at, PermNegation(amount))
    }
  }

  def subtractMask(origMask: Term, removedMask: Term, resource: Any, program: ast.Program, v: Verifier): Term = {
    if (!simplifyOnConsume) {
      return MaskDiff(origMask, removedMask)
    }

    val termAdditions = mutable.LinkedHashMap[Term, Term]()
    val termRemovals = mutable.LinkedHashMap[Term, Term]()
    val maskAdditions = mutable.LinkedHashSet[Term]()
    val maskRemovals = mutable.LinkedHashSet[Term]()

    var done = false
    var foundTerm: Option[Term] = None

    def traverse(mask: Term): Unit = mask match {
      case MaskAdd(m, r, PermNegation(v)) => termRemovals.update(r, v); traverse(m)
      case MaskAdd(m, r, v) => termAdditions.update(r, v); traverse(m)
      case MaskSum(m1, m2) => traverse(m1); traverse(m2)
      case MaskDiff(m1, m2) => maskRemovals.add(m2); traverse(m1)
      case ZeroMask =>
      case PredZeroMask =>
      case t => maskAdditions.add(t)
    }

    traverse(origMask)

    foundTerm = maskAdditions.find(_ == removedMask)

    if (!foundTerm.isDefined) {
      val additions = maskAdditions.toSeq.distinct

      val argSorts = resource match {
        case _: ast.Field => Seq(sorts.Ref)
        case p: ast.Predicate => p.formalArgs.map(l => v.symbolConverter.toSort(l.typ))
        case mwi: MagicWandIdentifier => mwi.ghostFreeWand.subexpressionsToEvaluate(program).map(e => v.symbolConverter.toSort(e.typ))
      }
      val args = argSorts.zipWithIndex.map(s => Var(Identifier(s"arg_v${s._2}"), s._1, false))
      val argTerm = if (resource.isInstanceOf[ast.Field]) args(0) else toSnapTree(args)
      val removedMaskLookup = HeapLookup(removedMask, argTerm)

      for (add <- additions) {
        if (!done) {
          val equality = Forall(args, HeapLookup(add, argTerm) === removedMaskLookup, Trigger(removedMaskLookup))
          if (v.decider.check(equality, 0)) {
            foundTerm = Some(add)
            done = true
          }
        }
      }
    }

    if (foundTerm.isDefined) {
      def replace(mask: Term): Term = mask match {
        case mask if foundTerm.isEmpty => mask
        case MaskAdd(m, r, v) => MaskAdd(replace(m), r, v)
        case MaskSum(m1, m2) if m1 == foundTerm.get =>
          foundTerm = None
          m2
        case MaskSum(m1, m2) if m2 == foundTerm.get =>
          foundTerm = None
          m1
        case MaskSum(m1, m2) => MaskSum(replace(m1), replace(m2))
        case MaskDiff(m1, m2) => MaskDiff(replace(m1), m2)
        case ZeroMask => mask
        case PredZeroMask => mask
        case t if t == foundTerm.get =>
          foundTerm = None
          if (origMask.sort == MaskSort) ZeroMask else PredZeroMask
        case t => t
      }
      val replaced = replace(origMask)
      replaced
    } else {
      MaskDiff(origMask, removedMask)
    }
  }

  def consumeSingleLocation(s: State,
                            h: Heap,
                            codomainQVars: Seq[Var], /* rs := r_1, ..., r_m */
                            arguments: Seq[Term], // es := e_1, ..., e_n
                            argumentsExp: Option[Seq[ast.Exp]],
                            resourceAccess: ast.ResourceAccess,
                            permissions: Term, /* p */
                            permissionsExp: Option[ast.Exp],
                            pve: PartialVerificationError,
                            v: Verifier,
                            resMap: Map[Any, Term])
                           (Q: (State, Heap, Term, Verifier) => VerificationResult)
  : VerificationResult = {
    val resource = resourceAccess.res(s.program)

    val resourceToFind = resource match {
      case mw: ast.MagicWand => MagicWandIdentifier(mw, s.program)
      case _ => resource
    }

    val argTerm = resource match {
      case _: ast.Field => arguments(0)
      case _: ast.Predicate => toSnapTree(arguments)
      case _: ast.MagicWand => toSnapTree(arguments)
    }

    if (s.exhaleExt) {
      val failure = resourceAccess match {
        case locAcc: ast.LocationAccess => createFailure(pve dueTo InsufficientPermission(locAcc), v, s, "single QP consume inside package")
        case wand: ast.MagicWand => createFailure(pve dueTo MagicWandChunkNotFound(wand), v, s, "single QP consume inside package")
        case _ => sys.error(s"Found resource $resourceAccess, which is not yet supported as a quantified resource.")
      }
      magicWandSupporter.transfer(s, permissions, permissionsExp, failure, Seq(), v)((s1, h1a, rPerm, rPermExp, v1) => {
        val (h1, resChunk) = resourceToFind match {
          case mwi: MagicWandIdentifier => findOrCreateMaskHeapChunk(h1a, mwi, v1)
          case r: ast.Resource => (h1a, findMaskHeapChunk(h1a, r))
        }

        val consumeExact = terms.utils.consumeExactRead(rPerm, s1.constrainableARPs)

        val maskValue = HeapLookup(resChunk.mask, argTerm)

        val hasAll = if (consumeExact) AtLeast(maskValue, rPerm) else Greater(maskValue, NoPerm)
        val hasNone = AtMost(maskValue, NoPerm)

        v.decider.check(hasNone, Verifier.config.splitTimeout()) match {
          case false =>
            if (!consumeExact) {
              // constrain wildcard
              v.decider.assume(PermLess(rPerm, maskValue), Option.when(withExp)(DebugExp.createInstance("Constrain wildcard permission")))
            }
            var newMask = MaskAdd(resChunk.mask, argTerm, PermNegation(rPerm))
            newMask = newMask match {
              case MaskAdd(resChunk.mask, argTerm, PermNegation(rPerm)) if !s.assertReadAccessOnly=> removeSingleAdd(resChunk.mask, argTerm, rPerm, s, v)
              case _ => newMask
            }

            val taken = PermMin(maskValue, rPerm)
            val remainingChunk = resChunk.copy(newMask = MaskAdd(resChunk.mask, argTerm, PermNegation(taken)))
            val consumedChunk = resChunk.copy(newMask = MaskAdd(if (resourceToFind.isInstanceOf[ast.Field]) ZeroMask else PredZeroMask, argTerm, taken))
            if (v.decider.check(hasAll, 0)) {
              (Complete(), s1, h1 - resChunk + remainingChunk, Some(consumedChunk))
            } else {
              (Incomplete(PermMinus(rPerm, taken), None), s1, h1 - resChunk + remainingChunk, Some(consumedChunk))
            }
          case true =>
            val remaining = rPerm
            (Incomplete(remaining, None), s1, h1, None)
        }
      })((s4, optCh, v2) =>
        optCh match {
          case Some(ch) =>
            val newSnapMask = MaskSum(resMap(resourceToFind), ch.mask)
            val snap = FakeMaskMapTerm(resMap.updated(resourceToFind, newSnapMask).asInstanceOf[immutable.ListMap[Any, Term]])
            Q(s4, s4.h, snap, v2)
          case _ =>
            Q(s4, s4.h, FakeMaskMapTerm(resMap.asInstanceOf[immutable.ListMap[Any, Term]]), v2)
        }
      )
    } else {
      val resChunk = findMaskHeapChunk(h, resourceToFind)

      val consumeExact = terms.utils.consumeExactRead(permissions, s.constrainableARPs)

      val maskValue = HeapLookup(resChunk.mask, argTerm)

      val sufficientPermCheck = if (consumeExact) AtLeast(maskValue, permissions) else Greater(maskValue, NoPerm)
      val completeSufficientPermCheck = Implies(FunctionPreconditionTransformer.transform(sufficientPermCheck, s.program), sufficientPermCheck)
      v.decider.assert(completeSufficientPermCheck) {
        case true =>
          if (!consumeExact) {
            // constrain wildcard
            v.decider.assume(PermLess(permissions, maskValue), Option.when(withExp)(DebugExp.createInstance("Wildcard constraint")))
          }
          var newMask = MaskAdd(resChunk.mask, argTerm, PermNegation(permissions))
          newMask = newMask match {
            case MaskAdd(resChunk.mask, argTerm, PermNegation(permissions)) if !s.assertReadAccessOnly => removeSingleAdd(resChunk.mask, argTerm, permissions, s, v)
            case _ => newMask
          }

          if (assumeGoodMask)
            v.decider.assume(if (resource.isInstanceOf[ast.Field]) GoodFieldMask(newMask) else GoodMask(newMask),
              Option.when(withExp)(DebugExp.createInstance("Valid mask")))

          val newChunk = if (s.functionRecorder != NoopFunctionRecorder || s.assertReadAccessOnly) {
            // no need to havoc
            resChunk.copy(newMask = newMask)
          } else {
            val freshHeap = v.decider.fresh("heap", resChunk.heap.sort, Option.when(withExp)(PUnknown()))
            v.decider.assume(IdenticalOnKnownLocations(resChunk.heap, freshHeap, newMask),
              Option.when(withExp)(DebugExp.createInstance("Framing heap", true)))
            resChunk.copy(newMask = newMask, newHeap = freshHeap)
          }

          val snapPermTerm = if (!consumeExact && s.assertReadAccessOnly) FullPerm else permissions
          val newSnapMask = MaskAdd(resMap(resourceToFind), argTerm, snapPermTerm)
          val snap = FakeMaskMapTerm(resMap.updated(resourceToFind, newSnapMask).asInstanceOf[immutable.ListMap[Any, Term]])
          // set up partially consumed heap
          Q(s, h - resChunk + newChunk, snap, v)
        case false =>
          val failure = resourceAccess match {
            case locAcc: ast.LocationAccess => createFailure(pve dueTo InsufficientPermission(locAcc), v, s, completeSufficientPermCheck, "single QP consume")
            case wand: ast.MagicWand => createFailure(pve dueTo MagicWandChunkNotFound(wand), v, s, completeSufficientPermCheck, "single QP consume")
            case _ => sys.error(s"Found resource $resourceAccess, which is not yet supported as a quantified resource.")
          }
          failure
      }
    }
  }

  def consume(s: State,
              h: Heap,
              resource: Any,
              qvars: Seq[Var],
              qvarExps: Option[Seq[ast.LocalVarDecl]],
              formalQVars: Seq[Var],
              formalQVarsExp: Option[Seq[ast.LocalVarDecl]],
              qid: String,
              optTrigger: Option[Seq[ast.Trigger]],
              tTriggers: Seq[Trigger],
              auxGlobals: Seq[Term],
              auxNonGlobals: Seq[Quantification],
              auxGlobalsExp: Option[InsertionOrderedSet[DebugExp]],
              auxNonGlobalsExp: Option[InsertionOrderedSet[DebugExp]],
              tCond: Term,
              eCond: Option[ast.Exp],
              tArgs: Seq[Term],
              eArgs: Option[Seq[ast.Exp]],
              tPerm: Term,
              ePerm: Option[ast.Exp],
              pve: PartialVerificationError,
              negativePermissionReason: => ErrorReason,
              notInjectiveReason: => ErrorReason,
              insufficientPermissionReason: => ErrorReason,
              v: Verifier,
              resMap: Map[Any, Term])
             (Q: (State, Heap, Term, Verifier) => VerificationResult)
  : VerificationResult = {

    val (inverseFunctions, imagesOfFormalQVars) =
      quantifiedChunkSupporter.getFreshInverseFunctions(
        qvars,
        qvarExps,
        And(tCond, IsPositive(tPerm)),
        tArgs,
        eArgs,
        formalQVars,
        formalQVarsExp,
        s.relevantQuantifiedVariables(tArgs).map(_._1),
        Option.when(withExp)(s.relevantQuantifiedVariables(tArgs).map(_._2.get)),
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

    val comment = "Nested auxiliary terms: globals"
    v.decider.prover.comment(comment)
    v.decider.assume(auxGlobals, Option.when(withExp)(DebugExp.createInstance(description = comment, children = auxGlobalsExp.get)), enforceAssumption = false)

    val comment2 = "Nested auxiliary terms: non-globals"
    v.decider.prover.comment(comment2)
    optTrigger match {
      case None =>
        /* No explicit triggers provided */
        v.decider.assume(
          auxNonGlobals.map(_.copy(
            vars = effectiveTriggersQVars,
            triggers = effectiveTriggers)), Option.when(withExp)(DebugExp.createInstance(description = comment2, children = auxNonGlobalsExp.get)), enforceAssumption = false)
      case Some(_) =>
        /* Explicit triggers were provided. */
        v.decider.assume(auxNonGlobals, Option.when(withExp)(DebugExp.createInstance(description = comment2, children = auxNonGlobalsExp.get)), enforceAssumption = false)
    }

    val nonNegImplication = Implies(tCond, perms.IsNonNegative(tPerm))
    val nonNegImplicationExp = eCond.map(c => ast.Implies(c, ast.PermGeCmp(ePerm.get, ast.NoPerm()())())(c.pos, c.info, c.errT))
    val nonNegTerm = Forall(qvars, Implies(FunctionPreconditionTransformer.transform(nonNegImplication, s.program), nonNegImplication), Nil)
    val nonNegExp = qvarExps.map(qv => ast.Forall(qv, Nil, nonNegImplicationExp.get)())

    v.decider.assert(nonNegTerm) {
      case true =>
        val loss = PermTimes(tPerm, s.permissionScalingFactor)
        val lossExp = ePerm.map(p => ast.PermMul(p, s.permissionScalingFactorExp.get)(p.pos, p.info, p.errT))

        val constrainPermissions = !consumeExactRead(loss, s.constrainableARPs)

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
        val completeReceiverInjectivityCheck = Implies(FunctionPreconditionTransformer.transform(receiverInjectivityCheck, s.program),
          receiverInjectivityCheck)
        v.decider.assert(completeReceiverInjectivityCheck) {
          case true =>
            val qvarsToInvOfLoc = inverseFunctions.qvarsToInversesOf(formalQVars)
            val condOfInvOfLoc = tCond.replace(qvarsToInvOfLoc)
            val lossOfInvOfLoc = loss.replace(qvarsToInvOfLoc)

            v.decider.prover.comment("Definitional axioms for inverse functions")
            v.decider.assume(inverseFunctions.definitionalAxioms.map(a => FunctionPreconditionTransformer.transform(a, s.program)),
              Option.when(withExp)(DebugExp.createInstance("Inverse Function Axioms", isInternal_ = true)), enforceAssumption = false)
            v.decider.assume(inverseFunctions.definitionalAxioms,
              Option.when(withExp)(DebugExp.createInstance("Inverse Function Axioms", isInternal_ = true)), enforceAssumption = false)

            val resourceToFind = resource match {
              case mw: ast.MagicWand => MagicWandIdentifier(mw, s.program)
              case _ => resource
            }

            val argTerm = resource match {
              case _: ast.Field => formalQVars(0)
              case _: ast.Predicate => toSnapTree(formalQVars)
              case _ => toSnapTree(formalQVars)
            }

            if (s.exhaleExt) {
              val failure = createFailure(pve dueTo insufficientPermissionReason, v, s, "consuming QP")
              magicWandSupporter.transfer(s, lossOfInvOfLoc, lossExp, failure, formalQVars, v)((s1, h1a, rPerm, rPermExp, v1) => {

                val (hp, currentChunk) = resourceToFind match {
                  case mwi: MagicWandIdentifier => findOrCreateMaskHeapChunk(h1a, mwi, v)
                  case r: ast.Resource => (h1a, findMaskHeapChunk(h1a, r))
                }

                // assert enough permissions
                val currentPerm = HeapLookup(currentChunk.mask, argTerm)

                val allPerms = if (constrainPermissions) {
                  Forall(formalQVars, Implies(condOfInvOfLoc, PermLess(NoPerm, currentPerm)), Seq(), "sufficientPerms")
                } else {
                  Forall(formalQVars, Implies(condOfInvOfLoc, PermAtMost(rPerm, currentPerm)), Seq(), "sufficientPerms")
                }

                // remove permissions
                val (qpMask, newFr) = {
                  val qpMask = v.decider.fresh("qpMask", if (resource.isInstanceOf[ast.Field]) MaskSort else PredMaskSort, Option.when(withExp)(PUnknown()))
                  val qpMaskGet = HeapLookup(qpMask, argTerm)
                  val conditionalizedPermissions = Ite(condOfInvOfLoc, PermMin(rPerm, currentPerm), NoPerm)
                  val qpMaskConstraint = Forall(formalQVars, qpMaskGet === conditionalizedPermissions, Seq(Trigger(qpMaskGet)), "qpMaskdef")
                  v.decider.assume(qpMaskConstraint, Option.when(withExp)(DebugExp.createInstance("QP mask definition")))
                  (qpMask, s.functionRecorder.recordFieldInv(inverseFunctions).recordConstrainedVar(qpMask, qpMaskConstraint))
                }

                val remainingMask = MaskDiff(currentChunk.mask, qpMask)
                val consumedChunk = currentChunk.copy(newMask = qpMask)
                val remainingChunk = currentChunk.copy(newMask = remainingMask)

                val qpMaskGet = HeapLookup(qpMask, argTerm)

                val s1p = s1.copy(functionRecorder = newFr)

                if (v.decider.check(allPerms, 0)) {
                  (Complete(), s1p, hp - currentChunk + remainingChunk, Some(consumedChunk))
                } else {
                  (Incomplete(PermMinus(rPerm, qpMaskGet), None), s1p, hp - currentChunk + remainingChunk, Some(consumedChunk))
                }
              })((s4, optCh, v2) => {
                optCh match {
                  case Some(ch) =>
                    val newSnapMask = MaskSum(resMap(resourceToFind), ch.mask)
                    val snap = FakeMaskMapTerm(resMap.updated(resourceToFind, newSnapMask).asInstanceOf[immutable.ListMap[Any, Term]])
                    Q(s4, s4.h, snap, v2)
                  case _ =>
                    Q(s4, s4.h, FakeMaskMapTerm(resMap.asInstanceOf[immutable.ListMap[Any, Term]]), v2)
                }
              })
            } else {
              val (hp, currentChunk) = resourceToFind match {
                case mwi: MagicWandIdentifier => findOrCreateMaskHeapChunk(h, mwi, v)
                case r: ast.Resource => (h, findMaskHeapChunk(h, r))
              }

              // assert enough permissions
              val currentPerm = HeapLookup(currentChunk.mask, argTerm)

              val argTermQvars = resource match {
                case _: ast.Field => tArgs(0)
                case _: ast.Predicate => toSnapTree(tArgs)
                case _ => toSnapTree(tArgs)
              }
              val currentPermQvars = HeapLookup(currentChunk.mask, argTermQvars)

              val sufficientPerm = if (constrainPermissions) {
                //Forall(formalQVars, Implies(condOfInvOfLoc, PermLess(NoPerm(), currentPerm)), Seq(), "sufficientPerms")
                Forall(qvars, Implies(tCond, PermLess(NoPerm, currentPermQvars)), tTriggers, "sufficientPerms")
              } else {
                //Forall(formalQVars, Implies(condOfInvOfLoc, PermAtMost(lossOfInvOfLoc, currentPerm)), Seq(), "sufficientPerms")
                Forall(qvars, Implies(tCond, PermAtMost(loss, currentPermQvars)), tTriggers, "sufficientPerms")
              }
              val completeSufficientPerm = Implies(FunctionPreconditionTransformer.transform(sufficientPerm, s.program), sufficientPerm)
              v.decider.assert(completeSufficientPerm)(r => r match {
                case true =>
                  if (constrainPermissions) {
                    // constrain wildcards
                    val permissionConstraint = Forall(formalQVars, Implies(condOfInvOfLoc, PermLess(lossOfInvOfLoc, currentPerm)), Seq(), "qpConstrainWildcard")
                    v.decider.assume(permissionConstraint, Option.when(withExp)(DebugExp.createInstance("Constrain wildcard")))
                  }

                  // remove permissions
                  val qpMask = v.decider.fresh("qpMask", if (resource.isInstanceOf[ast.Field]) MaskSort else PredMaskSort, Option.when(withExp)(PUnknown()))
                  val qpMaskGet = HeapLookup(qpMask, argTerm)
                  val conditionalizedPermissions = Ite(condOfInvOfLoc, lossOfInvOfLoc, NoPerm)
                  val qpMaskConstraint = Forall(formalQVars, qpMaskGet === conditionalizedPermissions, Seq(Trigger(qpMaskGet)), "qpMaskdef")
                  v.decider.assume(qpMaskConstraint, Option.when(withExp)(DebugExp.createInstance("QP mask definition")))
                  val newFr = s.functionRecorder.recordFieldInv(inverseFunctions).recordConstrainedVar(qpMask, qpMaskConstraint)

                  // simplify only if this mask will be used later
                  val newMask = if (s.assertReadAccessOnly) MaskDiff(currentChunk.mask, qpMask) else subtractMask(currentChunk.mask, qpMask, resource, s.program, v)
                  if (assumeGoodMask)
                    v.decider.assume(if (resource.isInstanceOf[ast.Field]) GoodFieldMask(newMask) else GoodMask(newMask),
                      Option.when(withExp)(DebugExp.createInstance("Valid mask")))

                  val newChunk = if (s.functionRecorder != NoopFunctionRecorder || s.assertReadAccessOnly) {
                    // no need to havoc
                    currentChunk.copy(newMask = newMask)
                  } else {
                    val freshHeap = v.decider.fresh("heap", currentChunk.heap.sort, Option.when(withExp)(PUnknown()))
                    v.decider.assume(IdenticalOnKnownLocations(currentChunk.heap, freshHeap, newMask),
                      Option.when(withExp)(DebugExp.createInstance("Framing heap", true)))
                    currentChunk.copy(newMask = newMask, newHeap = freshHeap)
                  }

                  // continue
                  val newHeap = hp - currentChunk + newChunk
                  val s2 = s.copy(functionRecorder = newFr, partiallyConsumedHeap = Some(newHeap))
                  val newSnapMask = MaskSum(resMap(resourceToFind), qpMask)
                  val snap = FakeMaskMapTerm(resMap.updated(resource, newSnapMask).asInstanceOf[immutable.ListMap[Any, Term]])
                  Q(s2, newHeap, snap, v)
                case false =>
                  createFailure (pve dueTo insufficientPermissionReason, v, s, completeSufficientPerm, "QP consume")
              })
            }
          case false =>
            createFailure(pve dueTo notInjectiveReason, v, s, completeReceiverInjectivityCheck, "QP receiver is injective")}
      case false =>
        createFailure(pve dueTo negativePermissionReason, v, s, nonNegTerm, nonNegExp)}
  }

  def produceSingleLocation(s: State,
                            resource: Any,
                            tArgs: Seq[Term],
                            tPerm: Term,
                            v: Verifier,
                            snap: Term)
                           (Q: (State, Verifier) => VerificationResult)
  : VerificationResult = {

    val resChunk = s.h.values.find(c => c.asInstanceOf[MaskHeapChunk].resource == resource).get.asInstanceOf[BasicMaskHeapChunk]
    val argTerm = resource match {
      case _: ast.Field => tArgs(0)
      case _: ast.Predicate => toSnapTree(tArgs)
      case _: MagicWandIdentifier => toSnapTree(tArgs)
    }
    val newMask = MaskAdd(resChunk.mask, argTerm, tPerm) // HeapUpdate(resChunk.mask, argTerm, PermPlus(HeapLookup(resChunk.mask, argTerm), tPerm))
    if (assumeGoodMask)
      v.decider.assume(if (resource.isInstanceOf[ast.Field]) GoodFieldMask(newMask) else GoodMask(newMask),
        Option.when(withExp)(DebugExp.createInstance("Valid mask")))
    val snapHeapMap = snap.asInstanceOf[FakeMaskMapTerm].masks

    val newHeap = MergeSingle(resChunk.heap, resChunk.mask, argTerm, HeapLookup(snapHeapMap(resource), argTerm))
    val ch = resChunk.copy(newMask = newMask, newHeap = newHeap)
    val h1 = s.h - resChunk + ch

    val permConstraint = if (resource.isInstanceOf[ast.Field])
      And(Implies(perms.IsPositive(tPerm), argTerm !== Null), PermAtMost(HeapLookup(ch.mask, argTerm), FullPerm))
    else True
    v.decider.assume(permConstraint, Option.when(withExp)(DebugExp.createInstance("Permission upper bound")))

    val s1 = s.copy(h = h1)
    Q(s1, v)
  }

  def produce(s: State,
              forall: ast.Forall,
              resource: Any,
              qvars: Seq[Var],
              qvarExps: Option[Seq[ast.LocalVarDecl]],
              formalQVars: Seq[Var],
              formalQVarExps: Option[Seq[ast.LocalVarDecl]],
              qid: String,
              optTrigger: Option[Seq[ast.Trigger]],
              tTriggers: Seq[Trigger],
              auxGlobals: Seq[Term],
              auxNonGlobals: Seq[Quantification],
              auxGlobalsExp: Option[InsertionOrderedSet[DebugExp]],
              auxNonGlobalsExp: Option[InsertionOrderedSet[DebugExp]],
              tCond: Term,
              eCond: Option[ast.Exp],
              tArgs: Seq[Term],
              eArgs: Option[Seq[ast.Exp]],
              tSnap: Term,
              tPerm: Term,
              ePerm: Option[ast.Exp],
              pve: PartialVerificationError,
              negativePermissionReason: => ErrorReason,
              notInjectiveReason: => ErrorReason,
              v: Verifier)
             (Q: (State, Verifier) => VerificationResult)
  : VerificationResult = {

    val gain = PermTimes(tPerm, s.permissionScalingFactor)

    val (inverseFunctions, imagesOfCodomain) =
      quantifiedChunkSupporter.getFreshInverseFunctions(
        qvars,
        qvarExps,
        And(tCond, IsPositive(tPerm)),
        tArgs,
        eArgs,
        formalQVars,
        formalQVarExps,
        s.relevantQuantifiedVariables(tArgs).map(_._1),
        Option.when(withExp)(s.relevantQuantifiedVariables(tArgs).map(_._2.get)),
        optTrigger.map(_ => tTriggers),
        qid,
        v)

    val qvarsToInversesOfCodomain = inverseFunctions.qvarsToInversesOf(formalQVars)

    val conditionalizedPermissions =
      Ite(
        And(And(imagesOfCodomain), tCond.replace(qvarsToInversesOfCodomain)),
        gain.replace(qvarsToInversesOfCodomain),
        NoPerm)

    val snapHeapMap = tSnap.asInstanceOf[FakeMaskMapTerm].masks

    val (qpMask, qpMaskFunc, constraintVars) = (v.decider.fresh("qpMask", if (resource.isInstanceOf[ast.Field]) MaskSort else PredMaskSort, Option.when(withExp)(PUnknown())), None, Seq())

    // forall r :: { get(qpMask, r) } get(qpMask, r) == conditionalizedPermissions
    val argTerm = resource match {
      case _: ast.Field => formalQVars(0)
      case _ => toSnapTree(formalQVars)
    }
    val qpMaskGet = HeapLookup(qpMask, argTerm)
    val qpMaskConstraint = Forall(formalQVars, qpMaskGet === conditionalizedPermissions, Seq(Trigger(qpMaskGet)), "qpMaskdef")

    val resourceToFind = resource match {
      case mw: ast.MagicWand => MagicWandIdentifier(mw, s.program)
      case _ => resource
    }

    val (hp, currentChunk) = resourceToFind match {
      case mwi: MagicWandIdentifier => findOrCreateMaskHeapChunk(s.h, mwi, v)
      case r: ast.Resource => (s.h, findMaskHeapChunk(s.h, r))
    }
    val newMask =  MaskSum(currentChunk.mask, qpMask)


    val newHeap = MergeHeaps(currentChunk.heap, currentChunk.mask, snapHeapMap(resource), qpMask)
    val newChunk = currentChunk.copy(newMask = newMask, newHeap = newHeap)
    val newMaskGet = HeapLookup(newMask, argTerm)


    val permBoundConstraint = resource match {
      case _: ast.Field => And(Forall(formalQVars, PermAtMost(newMaskGet, FullPerm), Seq(Trigger(newMaskGet)), "qp_produce_upper_bound"),
        Forall(formalQVars, Implies(And(And(And(imagesOfCodomain), tCond.replace(qvarsToInversesOfCodomain)), PermLess(NoPerm, gain.replace(qvarsToInversesOfCodomain))), formalQVars(0) !== Null), Seq(), "qp_recvr_non_null"))
      case _ => True
    }

    val (effectiveTriggers, effectiveTriggersQVars) =
      optTrigger match {
        case Some(_) =>
          // triggers were translated with the old heap and mask, but we actually want to trigger on accesses on the new heap and mask.
          val newHeapTriggers = tTriggers.map(t => {
            val newTerms: Seq[Term] = t.p.map(trm => trm match {
              case HeapLookup(currentChunk.heap, r) => HeapLookup(newHeap, r)
              case HeapLookup(currentChunk.mask, r) => HeapLookup(qpMask, r)
              case _ => trm
            })

            Trigger(newTerms)
          })
          (newHeapTriggers, qvars)
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

    val commentGlobals = "Nested auxiliary terms: globals"
    v.decider.prover.comment(commentGlobals)
    v.decider.assume(auxGlobals, Option.when(withExp)(DebugExp.createInstance(description = commentGlobals, children = auxGlobalsExp.get)),
      enforceAssumption = false)

    val commentNonGlobals = "Nested auxiliary terms: non-globals"
    v.decider.prover.comment(commentNonGlobals)
    v.decider.assume(
      auxNonGlobals.map(_.copy(
        vars = effectiveTriggersQVars,
        triggers = effectiveTriggers)),
      Option.when(withExp)(DebugExp.createInstance(description = commentNonGlobals, children = auxNonGlobalsExp.get)), enforceAssumption = false)

    val nonNegImplication = Implies(tCond, perms.IsNonNegative(tPerm))
    val nonNegImplicationExp = eCond.map(c => ast.Implies(c, ast.PermGeCmp(ePerm.get, ast.NoPerm()())())(c.pos, c.info, c.errT))
    val nonNegTerm = Forall(qvars, Implies(FunctionPreconditionTransformer.transform(nonNegImplication, s.program), nonNegImplication), Nil)
    val nonNegExp = qvarExps.map(qv => ast.Forall(qv, Nil, nonNegImplicationExp.get)())
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
            True
          }
        v.decider.prover.comment("Check receiver injectivity")
        val completeReceiverInjectivityCheck = Implies(FunctionPreconditionTransformer.transform(receiverInjectivityCheck, s.program),
          receiverInjectivityCheck)
        v.decider.assert(completeReceiverInjectivityCheck) {
          case true =>
            v.decider.assume(qpMaskConstraint, Option.when(withExp)(DebugExp.createInstance("QP mask definition")))

            if (assumeGoodMask)
              v.decider.assume(if (resource.isInstanceOf[ast.Field]) GoodFieldMask(newMask) else GoodMask(newMask),
                Option.when(withExp)(DebugExp.createInstance("Valid mask")))

            val ax = inverseFunctions.axiomInversesOfInvertibles
            val inv = inverseFunctions.copy(axiomInversesOfInvertibles = Forall(ax.vars, ax.body, effectiveTriggers))

            val comment = "Definitional axioms for inverse functions"
            v.decider.prover.comment(comment)
            val definitionalAxiomMark = v.decider.setPathConditionMark()
            v.decider.assume(inv.definitionalAxioms.map(a => FunctionPreconditionTransformer.transform(a, s.program)),
              Option.when(withExp)(DebugExp.createInstance(comment, isInternal_ = true)), enforceAssumption = false)
            v.decider.assume(inv.definitionalAxioms, Option.when(withExp)(DebugExp.createInstance(comment, isInternal_ = true)), enforceAssumption = false)
            val conservedPcs =
              if (s.recordPcs) (s.conservedPcs.head :+ v.decider.pcs.after(definitionalAxiomMark)) +: s.conservedPcs.tail
              else s.conservedPcs

            val h1 = hp - currentChunk + newChunk
            v.decider.assume(permBoundConstraint, Option.when(withExp)(DebugExp.createInstance("Permission upper bound")))
            val newFr = s.functionRecorder.recordFieldInv(inv).recordConstrainedVar(qpMask, qpMaskConstraint)

            val s1 =
              s.copy(h = h1,
                functionRecorder = newFr,
                conservedPcs = conservedPcs)
            Q(s1, v)
          case false =>
            createFailure(pve dueTo notInjectiveReason, v, s, completeReceiverInjectivityCheck, "QP receiver is injective")}
      case false =>
        createFailure(pve dueTo negativePermissionReason, v, s, nonNegTerm, nonNegExp)}
  }
}