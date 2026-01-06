// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2022 ETH Zurich.

package viper.silicon.rules

import viper.silicon.debugger.DebugExp
import viper.silicon.interfaces.VerificationResult
import viper.silicon.rules.evaluator.{eval, evalQuantified, evals}
import viper.silicon.state._
import viper.silicon.state.terms._
import viper.silicon.verifier.Verifier
import viper.silver.ast
import viper.silver.verifier.errors.{HavocallFailed, QuasihavocFailed}
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

    eval(s, lhsExpr, pve, v)((s0, lhsTerm, _, v0) => {
      evals(s0, havoc.exp.args(s0.program), _ => pve, v0)((s1, tRcvrs, _, v1) => {
        val resource = havoc.exp.res(s1.program)

        // Call the havoc helper function, which returns a new heap, which is
        // partially havocked. Since we are executing a Havoc statement, we wrap
        // the HavocHelperData inside of a HavocOneData case (as opposed to HavocAllData).
        val condInfo = HavocOneData(tRcvrs)
        val newHeap = v1.heapSupporter.havocResource(s1, lhsTerm, resource, condInfo, v1)

        Q(s1.copy(h = newHeap), v1)
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
      es2   = eRsc.args(s.program), // The arguments to our resource. Evaluated assuming the condition is true
      optTriggers = None, // Triggers: none needed for Havocall
      name  = qid,
      pve   = pve,
      v     = v)
    {
      case (s1, tVars, eVars, Seq(tCond), _, Some((tArgs, eArgs, Seq(), _, _)), v1) =>
        // Seq() represents an empty list of Triggers
        // TODO: unnamed arguments are (tAuxGlobal, tAux) and (auxGlobalsExp, auxNonGlobalsExp). How should these be handled?

        val resource = eRsc.res(s1.program)
        val (codomainQVars, codomainQVarsExp) = getCodomainQVars(s1, resource, v1)

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

        val injectivityDebugExp = Option.when(withExp)(DebugExp.createInstance("QP receiver injectivity check is well-defined", true))
        v.decider.assume(FunctionPreconditionTransformer.transform(receiverInjectivityCheck, s.program), injectivityDebugExp)
        v.decider.assert(receiverInjectivityCheck) {
          case false => createFailure(pve dueTo notInjectiveReason, v, s1, receiverInjectivityCheck, "QP receiver injective")
          case true =>
            // Generate the inverse axioms
            val (inverseFunctions, imagesOfCodomain) = quantifiedChunkSupporter.getFreshInverseFunctions(
              qvars = tVars,
              qvarExps = eVars,
              condition = tCond,
              invertibles = tArgs,
              invertibleExps = eArgs,
              codomainQVars = codomainQVars,
              codomainQVarExps = codomainQVarsExp,
              additionalInvArgs = Seq(), // There are no additional quantified vars
              additionalInvArgExps = Option.when(withExp)(Seq()),
              stateQVars = Seq(),
              userProvidedTriggers = None,
              qidPrefix = qid,
              v = v1
            )
            val comment = "Definitional axioms for havocall inverse functions"
            v.decider.prover.comment(comment)
            v.decider.assume(inverseFunctions.definitionalAxioms, Option.when(withExp)(DebugExp.createInstance(comment, isInternal_ = true)), enforceAssumption = false)

            // Call the havoc helper function, which returns a new heap, which is
            // partially havocked. Since we are executing a Havocall statement, we wrap
            // the HavocHelperData inside of a HavocAllData case.
            val condInfo = HavocallData(inverseFunctions, codomainQVars, imagesOfCodomain)
            val newHeap = v1.heapSupporter.havocResource(s1, tCond, resource, condInfo, v1)

            Q(s1.copy(h = newHeap), v1)
        }
      case (s1, _, _, _, _, None, v1) => Q(s1, v1)
    }
  }

  private def resourceName(s: State, resacc: ast.ResourceAccess): String = {
    resacc match {
      case ast.FieldAccess(_, field) => field.name
      case ast.PredicateAccess(_, name) => name
      case wand: ast.MagicWand => MagicWandIdentifier(wand, s.program).toString
    }
  }

  // Get the variables that we must quantify over for each resource type
  private def getCodomainQVars(s: State, eRsc: ast.Resource, v: Verifier): (Seq[Var], Option[Seq[ast.LocalVarDecl]]) = {
    (s.getFormalArgVars(eRsc, v), Option.when(withExp)(s.getFormalArgDecls(eRsc)))
  }
}
