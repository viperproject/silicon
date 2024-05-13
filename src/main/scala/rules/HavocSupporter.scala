// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2022 ETH Zurich.

package viper.silicon.rules

import viper.silicon.interfaces.VerificationResult
import viper.silicon.interfaces.state.{Chunk, NonQuantifiedChunk}
import viper.silicon.Map
import viper.silicon.rules.evaluator.{eval, evalQuantified, evals}
import viper.silicon.rules.quantifiedChunkSupporter.freshSnapshotMap
import viper.silicon.state.terms._
import viper.silicon.state._
import viper.silicon.state.terms.predef.{`?r`, `?s`}
import viper.silicon.utils.freshSnap
import viper.silicon.verifier.Verifier
import viper.silver.ast
import viper.silver.verifier.errors.{QuasihavocFailed, HavocallFailed}
import viper.silver.verifier.reasons.QuasihavocallNotInjective

object havocSupporter extends SymbolicExecutionRules {

  // This type contains data that is needed to calculate condition guarding whether we
  // should replace the snapshot. Different data is needed for `havoc` and `havocall`.
  // For more information, see `replacementCond`.
  sealed trait HavocHelperData
  case class HavocallData(inverseFunctions: InverseFunctions, codomainQVars: Seq[Var], imagesOfCodomain: Seq[Term]) extends HavocHelperData
  case class HavocOneData(args: Seq[Term]) extends HavocHelperData

  /** Execute the statement `havoc c ==> R`, where c is a conditional expression and
    * R is any non-quantified resource (field, predicate, or wand).
    *
    * Evaluates the necessary expressions, then calls necessary helper function depending
    * on if our heap contains quantified or non-quantified permissions.
    */
  def execHavoc(havoc: ast.Quasihavoc,
                v: Verifier,
                s: State)
                (Q: (State, Verifier) => VerificationResult)
               : VerificationResult = {

    val pve = QuasihavocFailed(havoc)

    // If there is no havoc condition, use True as the condition
    val lhsExpr = havoc.lhs.getOrElse(ast.TrueLit()(havoc.pos))

    eval(s, lhsExpr, pve, v)((s0, lhsTerm, v0) => {
      evals(s0, resourceArgs(s0, havoc.exp), _ => pve, v0)((s1, tRcvrs, v1) => {
        val resource = havoc.exp.res(s1.program)

        // Call the havoc helper function, which returns a new set of chunks, some of
        // which may be havocked. Since we are executing a Havoc statement, we wrap
        // the HavocHelperData inside of a HavocOneData case (as opposed to HavocAllData).
        val newChunks =
          if (usesQPChunks(s1, resource))
            havocQuantifiedResource(s1, lhsTerm, resource, HavocOneData(tRcvrs), v1)
          else
            havocNonQuantifiedResource(s1, lhsTerm, resource, HavocOneData(tRcvrs), v1)

        Q(s1.copy(h = Heap(newChunks)), v1)
      })
    })
  }

  /** Execute the statement `havocall z: T :: c(z) ==> R(e1(z), ..., en(z))`. There may be more than one
    * quantified variable. c(z) is a conditional expression, and R(z) is a non-quantified
    * resource. Like execHavoc, this function evaluates the expressions, and then calls
    * the necessary helper function depending on if there are quantified or non-quantified
    * permissions in our heap.
    *
    * Let e map z --> (e1, ..., en). Like with quantified permissions, we require that e is injective.
    * After we evaluate all expressions, we must
    * 1. Verify that e is injective (fail otherwise)
    * 2. Axiomatize the inverse function e'. We use helper functions from quantified resources.
    */
  def execHavocall(havocall: ast.Quasihavocall,
                   v: Verifier,
                   s: State)
                   (Q: (State, Verifier) => VerificationResult)
                  : VerificationResult = {

    val pve = HavocallFailed(havocall)
    val ast.Quasihavocall(vars, lhs, eRsc) = havocall
    val qid = resourceName(s, eRsc)

    // If there is no havoc condition, use True as the condition
    val lhsExpr = lhs.getOrElse(ast.TrueLit()(havocall.pos))

    // Use evalQuantified to evaluate the expressions in our Havocall statement.
    // This helper function was intended for evaluating quantified expressions, like forall
    // and exists. However, it is also used for evaluating components of quantified permissions,
    // and does exactly what we want for evaluating components of Havocall. In particular,
    // It evaluates the resource expressions assuming that the condition holds.
    evalQuantified(
      s     = s,
      quant = Forall,
      vars  = vars, // The quantified variables
      es1   = Seq(lhsExpr), // The havoc condition. Evaluated and added as a path conditions
      es2   = resourceArgs(s, eRsc), // The arguments to our resource. Evaluated assuming the condition is true
      optTriggers = None, // Triggers: none needed for Havocall
      name  = qid,
      pve   = pve,
      v     = v)
    {
      case (s1, tVars, Seq(tCond), Some((tArgs, Seq(), _)), v1) =>
        // Seq() represents an empty list of Triggers
        // TODO: unnamed argument is (tAuxGlobal, tAux). How should these be handled?

        val resource = eRsc.res(s1.program)
        val codomainQVars = getCodomainQVars(s1, resource, v1)

        // Verify that the function z --> (e1(z), ..., en(z)) is injective
        val receiverInjectivityCheck =
          quantifiedChunkSupporter.injectivityAxiom(
            qvars     = tVars,
            condition = tCond,
            perms     = FullPerm,
            arguments = tArgs,
            triggers  = Nil,
            qidPrefix = qid,
            program   = s1.program)

        v.decider.prover.comment("Check havocall receiver injectivity")
        val notInjectiveReason = QuasihavocallNotInjective(havocall)

        v.decider.assume(FunctionPreconditionTransformer.transform(receiverInjectivityCheck, s.program))
        v.decider.assert(receiverInjectivityCheck) {
          case false => createFailure(pve dueTo notInjectiveReason, v, s1)
          case true =>
            // Generate the inverse axioms
            val (inverseFunctions, imagesOfCodomain) = quantifiedChunkSupporter.getFreshInverseFunctions(
              qvars = tVars,
              condition = tCond,
              invertibles = tArgs,
              codomainQVars = codomainQVars,
              additionalInvArgs = Seq(), // There are no additional quantified vars
              userProvidedTriggers = None,
              qidPrefix = qid,
              v = v1
            )
            v.decider.prover.comment("Definitional axioms for havocall inverse functions")
            v.decider.assume(inverseFunctions.definitionalAxioms)

            // Call the havoc helper function, which returns a new set of chunks, some of
            // which may be havocked. Since we are executing a Havocall statement, we wrap
            // the HavocHelperData inside of a HavocAllData case.
            val newChunks =
              if (usesQPChunks(s1, resource))
                havocQuantifiedResource(s1, tCond, resource, HavocallData(inverseFunctions, codomainQVars, imagesOfCodomain), v1)
              else
                havocNonQuantifiedResource(s1, tCond, resource, HavocallData(inverseFunctions, codomainQVars, imagesOfCodomain), v1)

            Q(s1.copy(h = Heap(newChunks)), v1)
        }
      case (s1, _, _, None, v1) => Q(s1, v1)
    }
  }

  /** Havoc a non-quantified resource. This helper function is used by havoc and havocall.
    * Suppose we want to havoc a resource R(e1, ..., en).
    * We filter the heap to only consider chunks with R. For each chunk R(vars; s, p), we
    * replace it with R(vars; s', p) where s' := ite(cond, fresh, s).
    * `cond` is calculated using `condInfo` by a helper function
    *
    * @param s the state
    * @param lhs the havoc condition
    * @param resource the type of resource we are havocking
    * @param condInfo the info needed to calculate the snapshot replace condition
    * @param v the verifier
    * @return all the chunks in the resulting heap
    */
  private def havocNonQuantifiedResource(s: State,
                                         lhs: Term,
                                         resource: ast.Resource,
                                         condInfo: HavocHelperData,
                                         v: Verifier)
                                        : Seq[Chunk] = {

    val id = ChunkIdentifier(resource, s.program)
    val (relevantChunks, otherChunks) = chunkSupporter.splitHeap[NonQuantifiedChunk](s.h, id)

    val newChunks = relevantChunks.map {
      case ch: MagicWandChunk =>
        val havockedSnap = freshSnap(sorts.Snap, v)
        val abstractLhs = freshSnap(sorts.Snap, v)
        val freshWandMap = v.decider.fresh("mwsf", sorts.MagicWandSnapFunction)
        val cond = replacementCond(lhs, ch.args, condInfo)

        // Define a new `MagicWandSnapshot` that checks the havoc condition when being applied
        val magicWandSnapshot = MagicWandSnapshot(abstractLhs, Ite(cond, havockedSnap, MWSFLookup(ch.snap.wandMap, abstractLhs)), freshWandMap)
        v.decider.assumeDefinition(magicWandSnapshot.definition)
        ch.withSnap(magicWandSnapshot)

      case ch =>
        val havockedSnap = freshSnap(ch.snap.sort, v)
        val cond = replacementCond(lhs, ch.args, condInfo)
        ch.withSnap(Ite(cond, havockedSnap, ch.snap))
    }
    otherChunks ++ newChunks
  }

  /** Havoc a quantified resource. This helper function is used by havoc and havocall.
    * Suppose we want to havoc a resource R(r1, ..., rn).
    * We filter the heap to only consider chunks with R. For each chunk R(rs; sm, pm), we
    * replace it with R(rs; sm', pm)
    * We axiomatize the new snapshot map sm' as follows:
    *   forall rs :: !cond(rs) ==> sm(rs) == sm'(rs)
    * the snapshot replacement condition `cond` is calculated by a helper function
    * This axiomatization provides no information about values which satisfy the snapshot
    * replacement condition, thus these snapshots are in essence, havocked.
    *
    * @param s the state
    * @param lhs the havoc condition
    * @param resource the resource type that we will havoc
    * @param condInfo data used to calculate the snapshot replacement function
    * @param v the verifier
    * @return all the chunks in the resulting heap
    */
  private def havocQuantifiedResource(s: State,
                                      lhs: Term,
                                      resource: ast.Resource,
                                      condInfo: HavocHelperData,
                                      v: Verifier)
                                     : Seq[Chunk] = {

    // Quantified field chunks are of the form R(r; sm, pm).
    // Conceptually, quantified predicate/wand chunks look like R(r1, ..., rn; sm, pm).
    // However, they are implemented as R(s; sm, pm). Thus, the snapshot map and permission
    // map take this aggregated quantifier s as input.
    // The arguments can be accessed via the snapshot destructors First and Second, e.g.
    //  r1 = First(s),
    //  r2 = First(Second(s)),
    //  ...
    val aggregateQvar = resource match {
      case _: ast.Field => `?r`
      case _ => `?s`
    }

    // Get the sequence of quantified variables (r1, ..., rn). For fields, this is the same
    // as aggregateQVar.
    val codomainQVars = getCodomainQVars(s, resource, v)

    val cond = replacementCond(lhs, codomainQVars, condInfo)

    // The condition is in terms of (r1, ..., rn). We must write it in terms of s.
    // Create the map from codomainQVars to expressions on the aggregateQVar, e.g.
    // r1 -> First(s), r2 -> First(Second(s)), etc.
    // Use this to rewrite cond in terms of s
    val codomainToAggregate: Map[Term, Term] =
      codomainQVars.zip(fromSnapTree(aggregateQvar, codomainQVars)).to(Map)
    val transformedCond = cond.replace(codomainToAggregate)

    val id = ChunkIdentifier(resource, s.program)
    val (relevantChunks, otherChunks) = quantifiedChunkSupporter.splitHeap[QuantifiedBasicChunk](s.h, id)

    val newChunks = relevantChunks.map { ch =>

      // Create a fresh snapshot map that we will axiomatize.
      // The argument additionalFvfArgs is an empty list because havocall statements cannot
      // be nested inside of quantifiers, thus it is impossible for us to be in a setting
      // with additional quantified variables.
      val newSm = freshSnapshotMap(s, resource, List(), v)

      // axiomatize the snapshot map:
      //  forall s: Snap :: !cond(s) ==> sm(s) == sm'(s)
      val lookupNew = ResourceLookup(resource, newSm, Seq(aggregateQvar), s.program)
      val lookupOld = ResourceLookup(resource, ch.snapshotMap, Seq(aggregateQvar), s.program)
      val newAxiom = Forall(
        aggregateQvar,
        Implies(Not(transformedCond), lookupOld === lookupNew),
        Seq(Trigger(lookupNew), Trigger(lookupOld)),
        s"qp.smValDef${v.counter(this).next()}",
        isGlobal = true,  // TODO: should the quantifier be global? Matches example in summarize_field
      )

      v.decider.prover.comment("axiomatized snapshot map after havoc")
      v.decider.assume(newAxiom)

      ch.withSnapshotMap(newSm)
    }
    newChunks ++ otherChunks
  }

  /** Construct the condition that determines if we should replace a snapshot.
    * If we have havoc lhs ==> R(e1, ..., en) and we encounter the chunk R(r1, ..., rn; _, _),
    * then we should replace the snapshot if
    *   cond := lhs && e1 == r1 && ... && en == rn
    * If we have havocall vs :: lhs(vs) ==> R(e1(vs), ..., en(vs)), then we assume that
    * e' is the inverse of the function (vs --> (e1(vs), ..., en(vs))).
    * If we encounter the chunk R(r1, ..., rn; _, _), then we should replace the snapshot if
    *   cond := lhs(e'(e1(vs), ..., en(vs)))
    * @param lhs the havoc condition
    * @param chunkArgs the arguments to the chunk (r1, ..., rn)
    * @param condInfo contains enough information to construct the snapshot replacement condition.
    *                 For havoc statements, it contains the variables (e1, ..., en)
    *                 For havocall statements, it contains the inverse function e'
    * @return the snapshot replacement condition
    */
  private def replacementCond(lhs: Term, chunkArgs: Seq[Term], condInfo: HavocHelperData): Term = {
    condInfo match {
      case HavocOneData(args) =>
        val eqs = And(chunkArgs.zip(args).map{ case (t1, t2) => t1 === t2 })
        And(lhs, eqs)
      case HavocallData(inverseFunctions, codomainQVars, imagesOfCodomain) =>
        val replaceMap = inverseFunctions.qvarsToInversesOf(chunkArgs)
        And(lhs.replace(replaceMap), And(imagesOfCodomain.map(_.replace(codomainQVars, chunkArgs))))
    }
  }

  private def resourceName(s: State, resacc: ast.ResourceAccess): String = {
    resacc match {
      case ast.FieldAccess(_, field) => field.name
      case ast.PredicateAccess(_, name) => name
      case wand: ast.MagicWand => MagicWandIdentifier(wand, s.program).toString
    }
  }

  private def resourceArgs(s: State, resacc: ast.ResourceAccess): Seq[ast.Exp] = {
    resacc match {
      case fa: ast.FieldAccess => fa.getArgs
      case pa: ast.PredicateAccess => pa.args
      case wand: ast.MagicWand => wand.subexpressionsToEvaluate(s.program)
    }
  }

  // Get the variables that we must quantify over for each resource type
  private def getCodomainQVars(s: State, eRsc: ast.Resource, v: Verifier): Seq[Var] = {
      eRsc match {
        case _: ast.Field => Seq(`?r`)
        case p: ast.Predicate =>
          s.predicateFormalVarMap(s.program.findPredicate(p.name))
        case w: ast.MagicWand =>
          val bodyVars = w.subexpressionsToEvaluate(s.program)
          bodyVars.indices.toList.map(i =>
              Var(Identifier(s"x$i"), v.symbolConverter.toSort(bodyVars(i).typ), false))
    }
  }

  // Return true if the heap uses quantified versions of these resources
  private def usesQPChunks(s: State, res: ast.Resource): Boolean = {
    res match {
      case f: ast.Field => s.qpFields.contains(f)
      case p: ast.Predicate => s.qpPredicates.contains(p)
      case w: ast.MagicWand => s.qpMagicWands.contains(MagicWandIdentifier(w, s.program))
    }
  }
}
