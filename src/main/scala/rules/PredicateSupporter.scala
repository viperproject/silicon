/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.rules

import viper.silver.ast
import viper.silver.verifier.PartialVerificationError
import viper.silicon.interfaces.{Failure, VerificationResult}
import viper.silicon.state._
import viper.silicon.state.terms._
import viper.silicon.verifier.Verifier
import viper.silicon.utils.toSf
import viper.silver.verifier.reasons.InsufficientPermission

trait PredicateSupportRules extends SymbolicExecutionRules {
  def fold(s: State,
           predicate: ast.Predicate,
           tArgs: List[Term],
           tPerm: Term,
           pve: PartialVerificationError,
           v: Verifier)
          (Q: (State, Verifier) => VerificationResult)
          : VerificationResult

  def unfold(s: State,
             predicate: ast.Predicate,
             tArgs: List[Term],
             tPerm: Term,
             pve: PartialVerificationError,
             v: Verifier,
             pa: ast.PredicateAccess /* TODO: Make optional */)
            (Q: (State, Verifier) => VerificationResult)
            : VerificationResult
}

object predicateSupporter extends PredicateSupportRules with Immutable {
  import producer._
  import consumer._

  def fold(s: State, predicate: ast.Predicate, tArgs: List[Term], tPerm: Term, pve: PartialVerificationError, v: Verifier)
          (Q: (State, Verifier) => VerificationResult)
          : VerificationResult = {

    val body = predicate.body.get /* Only non-abstract predicates can be unfolded */
    val gIns = s.g + Store(predicate.formalArgs map (_.localVar) zip tArgs)
    val s1 = s.copy(g = gIns,
                    fvfAsSnap = true,
                    psfAsSnap = true)
              .scalePermissionFactor(tPerm)
    consume(s1, body, pve, v)((s2, snap, v1) => {
      val predTrigger = App(Verifier.predicateData(predicate).triggerFunction,
                            snap.convert(terms.sorts.Snap) +: tArgs)
      v1.decider.assume(predTrigger)
      if (s2.qpPredicates.contains(predicate)) {
        //convert snapshot to desired type if necessary
        val snapConvert = snap.convert(s2.predicateSnapMap(predicate))
        val formalArgs = predicate.formalArgs.map(formalArg => Var(Identifier(formalArg.name), v1.symbolConverter.toSort(formalArg.typ)))
        val (psf, optPsfDef) = quantifiedPredicateChunkSupporter.createSingletonPredicateSnapFunction(predicate, tArgs, formalArgs, snapConvert, s2.predicateSnapMap, v1)
        optPsfDef.foreach(psfDef => v1.decider.assume(psfDef.domainDefinitions ++ psfDef.snapDefinitions))
        //create single quantified predicate chunk with given snapshot
        val ch = quantifiedPredicateChunkSupporter.createSingletonQuantifiedPredicateChunk(tArgs, formalArgs, predicate.name, psf, tPerm)
        Q(s2.copy(g = s.g, h = s2.h + ch) , v1)
      } else {
        val ch = PredicateChunk(predicate.name, tArgs, snap.convert(sorts.Snap), tPerm)
        val s3 = s2.copy(g = s.g,
                         fvfAsSnap = s.fvfAsSnap,
                         psfAsSnap = s.psfAsSnap,
                         permissionScalingFactor = s.permissionScalingFactor)
        chunkSupporter.produce(s3, s3.h, ch, v1)((s4, h1, v2) =>
          Q(s4.copy(h = h1), v2))
      }
    })
  }

  def unfold(s: State,
             predicate: ast.Predicate,
             tArgs: List[Term],
             tPerm: Term,
             pve: PartialVerificationError,
             v: Verifier,
             pa: ast.PredicateAccess)
            (Q: (State, Verifier) => VerificationResult)
            : VerificationResult = {

    /* [2016-05-09 Malte] The comment below appears to no longer be valid (in
     * Silicon revision aa8932f340ca). It is not unlikely that the originally
     * observed issue was actually caused by a different problem, because the
     * predicate body (with the formal predicate argument bound to some term)
     * does not occur in any heap-dependent function, and thus does not need to
     * be translated.
     *
     * [2014-12-10 Malte] Changing the store (insγ) doesn't play nicely with the
     * snapshot recorder because it might result in the same local variable
     * being bound to different terms, e.g., in the case of fun3 at the end of
     * functions/unfolding.sil, where the formal predicate argument x is bound
     * to y and y.n.
     */

    val gIns = s.g + Store(predicate.formalArgs map (_.localVar) zip tArgs)
    val body = predicate.body.get /* Only non-abstract predicates can be unfolded */
    val s1 = s.scalePermissionFactor(tPerm)
    if (s1.qpPredicates.contains(predicate)) {
      val formalVars:Seq[Var] = s1.predicateFormalVarMap(predicate)
      val hints = quantifiedPredicateChunkSupporter.extractHints(None, None, tArgs)
      val chunkOrderHeuristics = quantifiedPredicateChunkSupporter.hintBasedChunkOrderHeuristic(hints)
      //remove permission for single predicate
      quantifiedPredicateChunkSupporter.splitSingleLocation(s1, s1.h, predicate, tArgs, formalVars, PermTimes(tPerm, tPerm), chunkOrderHeuristics, v) {
        case Some((s2, h2, ch, psfDef)) =>
          val psfDomain = if (s2.fvfAsSnap) psfDef.domainDefinitions else Seq.empty
          v.decider.assume(psfDomain ++ psfDef.snapDefinitions)
          //evaluate snapshot value
          val snap = ch.valueAt(tArgs)
          val s3 = s2.copy(g = gIns, h = h2)
          produce(s3, toSf(snap), body, pve, v)((s4, v1) => {
            v1.decider.assume(App(Verifier.predicateData(predicate).triggerFunction, snap.convert(terms.sorts.Snap) +: tArgs))
            Q(s4.copy(g = s.g), v1)})

        case None => Failure(pve dueTo InsufficientPermission(pa))
      }
    } else {
      /*
      chunkSupporter.consume(σ, σ.h, predicate.name, tArgs, tPerm, pve, c, pa)((h1, snap, c1) => {
        produce(σ \ h1 \ insγ, s => snap.convert(s), tPerm, body, pve, c1)((σ2, c2) => {
          decider.assume(App(predicateData(predicate).triggerFunction, snap +: tArgs))
          Q(σ2 \ σ.γ, c2)})})*/
      chunkSupporter.consume(s1, s1.h, predicate.name, tArgs, s1.permissionScalingFactor, pve, v, pa)((s2, h1, snap, v1) => {
        val s3 = s2.copy(g = gIns,
                         h = h1)
        produce(s3, toSf(snap), body, pve, v1)((s4, v2) => {
          val predTrigger = App(Verifier.predicateData(predicate).triggerFunction, snap +: tArgs)
          v2.decider.assume(predTrigger)
          val s5 = s4.copy(g = s2.g,
                           permissionScalingFactor = s.permissionScalingFactor)
          Q(s5, v2)})})
    }
  }

/* NOTE: Possible alternative to storing the permission scaling factor in the context
 *       or passing it to produce/consume as an explicit argument.
 *       Carbon uses Permissions.multiplyExpByPerm as well (but does not extend the
 *       store).
 */
//    private def scale(γ: ST, body: ast.Exp, perm: Term) = {
//      /* TODO: Ensure that variable name does not clash with any Silver identifier already in use */
//      val scaleFactorVar = ast.LocalVar(identifierFactory.fresh("p'unf").name)(ast.Perm)
//      val scaledBody = ast.utility.Permissions.multiplyExpByPerm(body, scaleFactorVar)
//
//      (γ + (scaleFactorVar -> perm), scaledBody)
//    }
}
