package viper.silicon.dependencyAnalysis.siliconComponents

import viper.silicon.Config
import viper.silicon.dependencyAnalysis._
import viper.silicon.dependencyAnalysis.cliTool.DependencyAnalysisTool
import viper.silicon.interfaces.VerificationResult
import viper.silicon.logger.{MemberSymbExLogger, SymbExLogger}
import viper.silicon.state.chunks._
import viper.silicon.verifier.{BaseVerifier, DefaultMainVerifier, Verifier, WorkerVerifier}
import viper.silver.ast
import viper.silver.reporter.Reporter

trait DependencyAnalysisAwareVerifier extends BaseVerifier with DependencyAnalysisDeciderProvider {

  override val chunkFactory: ChunkFactory = new DependencyAwareChunkFactory(DADecider)

}

class DependencyAnalysisAwareMainVerifier(config: Config,
                                          override val reporter: Reporter,
                                          override val rootSymbExLogger: SymbExLogger[_ <: MemberSymbExLogger])
  extends DefaultMainVerifier(config, reporter, rootSymbExLogger)
    with DependencyAnalysisAwareVerifier
    with DependencyAnalysisAwareFunctionVerification {

  override protected lazy val _verificationPoolManager: DependencyAwareVerificationPoolManager = new DependencyAwareVerificationPoolManager(this)

  override def verificationPoolManager: DependencyAwareVerificationPoolManager = _verificationPoolManager

  override def createWorkerVerifier(): DependencyAnalysisAwareWorkerVerifier = new DependencyAnalysisAwareWorkerVerifier(this, nextUniqueVerifierId(), reporter, debugMode)

  override def allProvers: AllProvers with DependencyAnalysisProverFeatures = DependencyAnalysisAwareAllProvers

  object DependencyAnalysisAwareAllProvers extends AllProvers with DependencyAnalysisProverFeatures

  override def verifyMember(doVerify: Unit => Seq[VerificationResult], v: Verifier, member: ast.Member): Seq[VerificationResult] = {
    v match {
      case daVerifier: DependencyAnalysisAwareVerifier =>
        daVerifier.decider.initDependencyAnalyzer(member, allProvers.getPreambleAnalysisNodes ++ daVerifier.decider.prover.getPreambleAnalysisNodes)
        val result = super.verifyMember(doVerify, daVerifier, member)
        daVerifier.decider.resetDependencyAnalyzer()
        result
      case _ => super.verifyMember(doVerify, v, member)
    }
  }

  override def afterVerification(verificationResults: List[VerificationResult], program: ast.Program, inputFile: Option[String]): Unit = {
    val dependencyAnalysisResult = DependencyAnalysisTool.runDependencyAnalysisWorkflow(verificationResults, program, inputFile)
    (reporter, dependencyAnalysisResult) match {
      case (analysisReporter: DependencyAnalysisReporter, Some(res)) =>
        analysisReporter.joinedDependencyGraphInterpreter = Some(res.getFullDependencyGraphInterpreter)
      case _ =>
    }
  }
}

class DependencyAnalysisAwareWorkerVerifier(mainVerifier: DependencyAnalysisAwareMainVerifier,
                                            uniqueId: String,
                                            override val reporter: Reporter,
                                            override val debugMode: Boolean)
  extends WorkerVerifier(mainVerifier, uniqueId, reporter, debugMode)
    with DependencyAnalysisAwareVerifier with DependencyAnalysisMethodVerification
