// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silicon.verifier

import viper.silicon.Config
import viper.silicon.decider.{DependencyAnalysisAwareDeciderProvider, DependencyAnalysisProverHandler}
import viper.silicon.dependencyAnalysis._
import viper.silicon.dependencyAnalysis.cliTool.DependencyAnalysisTool
import viper.silicon.dependencyAnalysis.graphInterpretation.IntraproceduralGraphResult
import viper.silicon.interfaces.{Failure, VerificationResult}
import viper.silicon.logger.{MemberSymbExLogger, SymbExLogger}
import viper.silicon.state.chunks._
import viper.silicon.state.terms.{Term, True}
import viper.silicon.supporters.DependencyAnalysisAwareMethodVerificationUnitProvider
import viper.silicon.supporters.functions.DependencyAnalysisAwareFunctionVerificationUnitProvider
import viper.silver.ast
import viper.silver.dependencyAnalysis.{DependencyAnalysisSourceInfo, EdgeType, JoinType, SimpleDependencyAnalysisJoin}
import viper.silver.reporter.Reporter

trait DependencyAnalysisAwareVerifier extends BaseVerifier with DependencyAnalysisAwareDeciderProvider {

  override val chunkFactory: ChunkFactory = new DependencyAnalysisAwareChunkFactory(DADecider)

  /** Adds an assertion node for each conjunct of the preconditions, to which the callers of the member are joined. */
  def addPreconditionNodes(pres: Seq[ast.Exp]): Unit = {
    pres.flatMap(_.topLevelConjuncts).flatMap(pc => {
      val analysisInfos = decider.defaultAnalysisInfos.addInfo(pc.info, pc).withJoinInfo(SimpleDependencyAnalysisJoin(DependencyAnalysisSourceInfo.createAnalysisSourceInfo(pc), JoinType.Sink, EdgeType.Up))
      decider.getDependencyAnalyzer.createAssertOrCheckNode(True, analysisInfos, isCheck = false)
    }).foreach(decider.getDependencyAnalyzer.addAssertionNode)
  }

  /** Records that the postconditions of a member without a body depend on its preconditions. */
  def addDependenciesForAbstractMember(pres: Seq[ast.Exp], posts: Seq[ast.Exp]): Unit =
    decider.getDependencyAnalyzer.addDependenciesForAbstractMembers(pres.flatMap(_.topLevelConjuncts), posts.flatMap(_.topLevelConjuncts), decider.defaultAnalysisInfos)

  /** Builds the final graph of the current member and stores it in the given verification result. */
  def attachIntraproceduralResult(result: VerificationResult, member: ast.Member): Unit = {
    val allErrors = (result :: result.previous.toList).collect { case failure: Failure => failure }
    result.intraproceduralGraphResult = decider.getDependencyAnalyzer.buildFinalGraph().map(new IntraproceduralGraphResult(_, allErrors, member))
  }

}

class DependencyAnalysisAwareMainVerifier(config: Config,
                                          override val reporter: Reporter,
                                          override val rootSymbExLogger: SymbExLogger[_ <: MemberSymbExLogger])
  extends DefaultMainVerifier(config, reporter, rootSymbExLogger)
    with DependencyAnalysisAwareVerifier
    with DependencyAnalysisAwareFunctionVerificationUnitProvider {

  override protected lazy val _verificationPoolManager: DependencyAnalysisAwareVerificationPoolManager = new DependencyAnalysisAwareVerificationPoolManager(this)

  override def verificationPoolManager: DependencyAnalysisAwareVerificationPoolManager = _verificationPoolManager

  override def createWorkerVerifier(): DependencyAnalysisAwareWorkerVerifier = new DependencyAnalysisAwareWorkerVerifier(this, nextUniqueVerifierId(), reporter, debugMode)

  override def allProvers: AllProvers with DependencyAnalysisProverHandler = DependencyAnalysisAwareAllProvers

  private object DependencyAnalysisAwareAllProvers extends AllProvers with DependencyAnalysisProverHandler {
    def assume(term: Term, label: Option[String]): Unit = {
      decider.prover.assume(term, label)
      _verificationPoolManager.pooledVerifiers.assume(term, label)
    }
  }

  override def verifyMember(doVerify: Unit => Seq[VerificationResult], v: Verifier, member: ast.Member): Seq[VerificationResult] = {
    v.decider.analysisHooks.beginMember(member, allProvers.getPreambleAnalysisNodes ++ _verificationPoolManager.getAllDAAxiomNodes)
    val result = super.verifyMember(doVerify, v, member)
    v.decider.analysisHooks.endMember()
    result
  }

  override def afterVerification(verificationResults: List[VerificationResult], program: ast.Program, inputFile: Option[String]): Unit = {
    val dependencyAnalysisResult = config.dependencyAnalysis.toOption.map(commands =>
      DependencyAnalysisTool.runDependencyAnalysisWorkflow(commands, config.dependencyAnalysisOptions, verificationResults, program, inputFile))
    (reporter, dependencyAnalysisResult) match {
      case (analysisReporter: DependencyAnalysisReporter, Some(res)) =>
        analysisReporter.finalGraphQueries = Some(res.finalGraphQueries)
      case _ =>
    }
  }
}

class DependencyAnalysisAwareWorkerVerifier(mainVerifier: DependencyAnalysisAwareMainVerifier,
                                            uniqueId: String,
                                            override val reporter: Reporter,
                                            override val debugMode: Boolean)
  extends WorkerVerifier(mainVerifier, uniqueId, reporter, debugMode)
    with DependencyAnalysisAwareVerifier with DependencyAnalysisAwareMethodVerificationUnitProvider
