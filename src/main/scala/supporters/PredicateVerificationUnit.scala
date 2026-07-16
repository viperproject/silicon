// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.supporters

import com.typesafe.scalalogging.Logger
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silver.ast
import viper.silver.ast.Program
import viper.silver.components.StatefulComponent
import viper.silver.verifier.errors._
import viper.silicon.decider.Decider
import viper.silicon.{Map, toMap}
import viper.silicon.interfaces.decider.ProverLike
import viper.silicon.state._
import viper.silicon.state.State.OldHeaps
import viper.silicon.state.terms._
import viper.silicon.interfaces._
import viper.silicon.rules.executionFlowController
import viper.silicon.supporters.functions.{ActualFunctionRecorder, FunctionRecorder, FunctionRecorderHandler, NoopFunctionRecorder}
import viper.silicon.verifier.{Verifier, VerifierComponent}
import viper.silicon.utils.{freshSnap, toSf}

class PredicateData(val predicate: ast.Predicate)
                   /* Note: Holding a reference to a fixed symbol converter (instead of going
                    *       through a verifier) is only safe if the converter is effectively
                    *       independent of the verifiers.
                    */
                   (private val symbolConvert: SymbolConverter) extends FunctionRecorderHandler {

  var predContents: Option[PredicateContentsTree] = None
  var params: Option[Seq[Var]] = None

  val argumentSorts = predicate.formalArgs map (fm => symbolConvert.toSort(fm.typ))

  val triggerFunction =
    Fun(Identifier(s"${predicate.name}%trigger"), sorts.Snap +: argumentSorts, sorts.Bool)

}

trait PredicateContentsTree

case class PredicateBranchNode(cond: Term, condExp: (ast.Exp, Option[ast.Exp]), left: PredicateContentsTree, right: PredicateContentsTree) extends PredicateContentsTree

case class PredicateLeafNode(heap: Heap, assumptions: InsertionOrderedSet[Term]) extends PredicateContentsTree

trait PredicateVerificationUnit
    extends VerifyingPreambleContributor[Sort, Decl, Term, ast.Predicate] {

  def data: Map[String, PredicateData]
}

trait DefaultPredicateVerificationUnitProvider extends VerifierComponent { v: Verifier =>
  def logger: Logger
  def decider: Decider
  def symbolConverter: SymbolConverter

  object predicateSupporter extends PredicateVerificationUnit with StatefulComponent {
    import viper.silicon.rules.producer._

    /*private*/ var predicateData: Map[String, PredicateData] = Map.empty

    def data = predicateData
    def units = predicateData.values.map(_.predicate).toSeq
    /* Preamble contribution */

    def analyze(program: Program): Unit = {
      this.predicateData = toMap(
        program.predicates map (pred => pred.name -> new PredicateData(pred)(symbolConverter)))
    }

    /* Predicate supporter generates no sorts */
    val sortsAfterAnalysis: Iterable[Sort] = Seq.empty
    def declareSortsAfterAnalysis(sink: ProverLike): Unit = ()

    def symbolsAfterAnalysis: Iterable[Fun] = {
      predicateData.values map (_.triggerFunction)
    }

    def declareSymbolsAfterAnalysis(sink: ProverLike): Unit = {
      sink.comment("Declaring predicate trigger functions")
      symbolsAfterAnalysis foreach (f => sink.declare(FunctionDecl(f)))
    }

    /* Predicate supporter generates no axioms */
    val axiomsAfterAnalysis: Iterable[Term] = Seq.empty
    def emitAxiomsAfterAnalysis(sink: ProverLike): Unit = ()

    /* Verification and subsequent preamble contribution */

    def verify(sInit: State, predicate: ast.Predicate): Seq[VerificationResult] = {
      logger.debug("\n\n" + "-" * 10 + " PREDICATE " + predicate.name + "-" * 10 + "\n")
      decider.prover.comment("%s %s %s".format("-" * 10, predicate.name, "-" * 10))

      openSymbExLogger(predicate)

      val ins = predicate.formalArgs.map(_.localVar)
      val snap = freshSnap(sorts.Snap, v)
      val argVars = ins.map(x => (x, decider.fresh(x)))
      var funcRecorder: FunctionRecorder = if (!Verifier.config.enableSimplifiedUnfolds()) {
        NoopFunctionRecorder
      } else {
        ActualFunctionRecorder(Right((predicate, Seq(snap) ++ argVars.map(_._2._1))))
      }

      val s = sInit.copy(g = Store(argVars),
                         h = v.heapSupporter.getEmptyHeap(sInit.program),
                         oldHeaps = OldHeaps(),
                         functionRecorder = funcRecorder)

      val err = PredicateNotWellformed(predicate)

      var branchResults: Seq[(Seq[Term], Seq[(ast.Exp, Option[ast.Exp])], Heap, InsertionOrderedSet[Term])] = Seq()


      val result = predicate.body match {
        case None =>
          Success()
        case Some(body) =>
          /*    locallyXXX {
                magicWandSupporter.checkWandsAreSelfFraming(σ.γ, σ.h, predicate, c)}
          &&*/  executionFlowController.locally(s, v)((s1, _) => {
                  produce(s1, toSf(snap), body, err, v)((s2, v2) => {
                    val branchConds = v2.decider.pcs.branchConditions.reverse
                    val branchCondExps = v2.decider.pcs.branchConditionExps.reverse
                    assert(branchConds.length == branchCondExps.length)
                    val heap = s2.h
                    val assumptions = v2.decider.pcs.assumptions
                    branchResults = branchResults :+
                      (branchConds, branchCondExps, heap, assumptions)
                    funcRecorder = funcRecorder.merge(s2.functionRecorder)
                    Success()
                  })})
      }

      val overallResult = if (predicate.body.isDefined && !result.isFatal && Verifier.config.enableSimplifiedUnfolds())
        Some(makePredTree(branchResults)) else None

      this.predicateData(predicate.name).predContents = overallResult
      this.predicateData(predicate.name).params = Some(Seq(snap) ++ argVars.map(_._2._1))
      this.predicateData(predicate.name).addRecorders(Seq(funcRecorder))

      symbExLog.closeMemberScope()
      Seq(result)
    }

    def makePredTree(branches: Seq[(Seq[Term], Seq[(ast.Exp, Option[ast.Exp])], Heap, InsertionOrderedSet[Term])]): PredicateContentsTree = {
      if (branches.head._1.isEmpty) {
        assert(branches.length == 1)
        PredicateLeafNode(branches.head._3, branches.head._4)
      } else {
        val branchCond = branches.head._1.head
        val branchCondExp = branches.head._2.head
        val (trueBranches, falseBranches) = branches.partition(_._1.head == branchCond)
        if (trueBranches.nonEmpty && falseBranches.nonEmpty) {
          val trueTree = makePredTree(trueBranches.map(brnchs => (brnchs._1.tail, brnchs._2.tail, brnchs._3, brnchs._4)))
          val falseTree = makePredTree(falseBranches.map(brnchs => (brnchs._1.tail, brnchs._2.tail, brnchs._3, brnchs._4)))
          PredicateBranchNode(branchCond, branchCondExp, trueTree, falseTree)
        } else if (trueBranches.nonEmpty) {
          makePredTree(trueBranches.map(brnchs => (brnchs._1.tail, brnchs._2.tail, brnchs._3, brnchs._4)))
        } else {
          assert(falseBranches.nonEmpty)
          makePredTree(falseBranches.map(brnchs => (brnchs._1.tail, brnchs._2.tail, brnchs._3, brnchs._4)))
        }
      }
    }

    /* Predicate supporter generates no sorts */
    val sortsAfterVerification: Iterable[Sort] = Seq.empty
    def declareSortsAfterVerification(sink: ProverLike): Unit = ()

    val symbolsAfterVerification: Iterable[Decl] =
      generateFunctionSymbolsAfterVerification collect { case Right(f) => f }

    def declareSymbolsAfterVerification(sink: ProverLike): Unit = {
      generateFunctionSymbolsAfterVerification foreach {
        case Left(comment) => sink.comment(comment)
        case Right(decl) => sink.declare(decl)
      }
    }

    private def generateFunctionSymbolsAfterVerification: Iterable[Either[String, Decl]] = {
      // TODO: It can currently happen that a pTaken macro (see QuantifiedChunkSupporter, def removePermissions)
      //       is recorded as a fresh macro before a snapshot map that is used in the macro definition (body)
      //       is recorded, which will yield a Z3 syntax error (undeclared symbol). To work around this,
      //       macros are declared last. This work-around shouldn't be necessary, though.
      val (macroDecls, otherDecls) =
      predicateData.values.flatMap(_.getFreshSymbolsAcrossAllPhases).partition(_.isInstanceOf[MacroDecl])

      Seq(Left("Declaring symbols related to program functions (from verification)")) ++
        otherDecls.map(Right(_)) ++
        macroDecls.map(Right(_))
    }

    /* Predicate supporter generates no axioms */
    val axiomsAfterVerification: Iterable[Term] = Seq.empty
    def emitAxiomsAfterVerification(sink: ProverLike): Unit = {
    }

    /* Lifetime */

    def start(): Unit = {}

    def reset(): Unit = {
      predicateData = predicateData.empty
    }

    def stop(): Unit = {}
  }
}
