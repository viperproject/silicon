// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2022 ETH Zurich.

package viper.silicon.rules

import viper.silicon.interfaces.VerificationResult
import viper.silicon.interfaces.state.CarbonChunk
import viper.silicon.rules.quantifiedChunkSupporter.createFailure
import viper.silicon.state.terms.{AtLeast, FakeMaskMapTerm, FullPerm, Greater, HeapLookup, HeapUpdate, IdenticalOnKnownLocations, MaskAdd, MergeSingle, NoPerm, PermAtMost, PermLess, PermMinus, PermPlus, Term, True, Var, sorts, toSnapTree}
import viper.silicon.state.{BasicCarbonChunk, ChunkIdentifier, Heap, State, terms}
import viper.silicon.supporters.functions.NoopFunctionRecorder
import viper.silicon.verifier.Verifier
import viper.silver.verifier.PartialVerificationError
import viper.silver.ast
import viper.silver.ast.PermAdd
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
          val newMask = MaskAdd(resChunk.mask, argTerm, PermMinus(NoPerm(), permissions))//HeapUpdate(resChunk.mask, argTerm, PermMinus(maskValue, permissions))
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



    // set up partially consumed heap


    /*
    val resource = resourceAccess.res(s.program)
    val failure = resourceAccess match {
      case locAcc: ast.LocationAccess => createFailure(pve dueTo InsufficientPermission(locAcc), v, s)
      case wand: ast.MagicWand => createFailure(pve dueTo MagicWandChunkNotFound(wand), v, s)
      case _ => sys.error(s"Found resource $resourceAccess, which is not yet supported as a quantified resource.")
    }

    val chunkIdentifier = ChunkIdentifier(resource, s.program)
    if (s.exhaleExt) {
      ???
    } else {
      // find chunk
      h.values.find {
        case cc: CarbonChunk if cc.id == chunkIdentifier => true
        case _ => false
      }

      // assert sufficient
      v.decider.assert()

      // create snapshot :( can i do this without droping lots of
    }

     */
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

    val permConstraint = if (resource.isInstanceOf[ast.Field]) PermAtMost(HeapLookup(ch.mask, argTerm), FullPerm()) else True()
    v.decider.assume(permConstraint)

    //TODO: assume trigger

    val s1 = s.copy(h = h1)
    Q(s1, v)
  }
}
