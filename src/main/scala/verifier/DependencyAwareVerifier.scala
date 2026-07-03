package viper.silicon.verifier

import viper.silicon.Config
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.decider.Mark
import viper.silicon.dependencyAnalysis._
import viper.silicon.dependencyAnalysis.cliTool.DependencyAnalysisTool
import viper.silicon.dependencyAnalysis.graphInterpretation.DependencyGraphInterpreter
import viper.silicon.interfaces.decider.ProverLike
import viper.silicon.interfaces.state.{Chunk, GeneralChunk}
import viper.silicon.interfaces.{Failure, VerificationResult}
import viper.silicon.logger.{MemberSymbExLogger, SymbExLogger}
import viper.silicon.state.terms._
import viper.silicon.state.{ChunkFactory, DependencyAwareChunkFactory, State}
import viper.silver.ast
import viper.silver.ast.{Info, Member, Method}
import viper.silver.dependencyAnalysis._
import viper.silver.reporter.Reporter

trait DependencyAnalysisAwareVerifier extends BaseVerifier {
	override def decider: DependencyAnalysisAwareDecider = DADecider
	override val chunkFactory: ChunkFactory = new DependencyAwareChunkFactory(DADecider)

	object DADecider extends DependencyAnalysisAwareDecider

	trait DependencyAnalysisAwareDecider extends AbstractDecider with DependencyAnalysisDeciderFeatures {

		override def handleInfeasiblePath(hasAssertions: Boolean, hasAssumptions: Boolean, analysisInfos: DependencyAnalysisInfos): Unit = {
			if (!isPathInfeasible) return
			super.handleInfeasiblePath(hasAssertions, hasAssumptions, analysisInfos)
			if (hasAssertions) {
				dependencyAnalyzer.addAssertionWithDepToInfeasNode(pcs.getCurrentInfeasibilityNode, analysisInfos)
			}
			if (hasAssumptions) {
				dependencyAnalyzer.addAssumption(True, analysisInfos)
			}
		}

		override def isDependencyAnalysisEnabled: Boolean = Verifier.config.enableDependencyAnalysis() && !dependencyAnalyzer.isInstanceOf[NoDependencyAnalyzer]

		override def initDependencyAnalyzer(member: Member, preambleNodes: Iterable[DependencyAnalysisNode]): Unit = {
			val isAnalysisEnabled = DependencyAnalyzer.extractEnableAnalysisFromInfo(member.info).getOrElse(Verifier.config.enableDependencyAnalysis())
			if (isAnalysisEnabled) {
				dependencyAnalyzer = new DefaultDependencyAnalyzer(Some(member))
				dependencyAnalyzer.addNodes(preambleNodes)
			} else {
				dependencyAnalyzer = new NoDependencyAnalyzer
			}
		}

		override def resetDependencyAnalyzer(): Unit = {
			dependencyAnalyzer = new NoDependencyAnalyzer
		}

		override def registerChunk[CH <: GeneralChunk](buildChunk: Term => CH, perm: Term, analysisInfos: DependencyAnalysisInfos, isExhale: Boolean): CH = {
			registerDerivedChunk(Set.empty, buildChunk, perm, analysisInfos, isExhale)
		}

		override def registerDerivedChunk[CH <: GeneralChunk](sourceChunks: Set[Chunk], buildChunk: Term => CH, perm: Term, analysisInfos: DependencyAnalysisInfos, isExhale: Boolean, createLabel: Boolean = true): CH = {
			if (!isDependencyAnalysisEnabled)
				return buildChunk(perm)

			val labelNodeOpt = getOrCreateAnalysisLabelNode()

			if (isExhale)
				dependencyAnalyzer.registerExhaleChunk(sourceChunks, buildChunk, perm, labelNodeOpt, analysisInfos)
			else {
				dependencyAnalyzer.registerInhaleChunk(sourceChunks, buildChunk, perm, labelNodeOpt, analysisInfos)
			}
		}

		private def getOrCreateAnalysisLabelNode(sourceChunks: Iterable[Chunk] = Set.empty, sourceTerms: Iterable[Term] = Set.empty): Option[LabelNode] = {
			if (!isDependencyAnalysisEnabled)
				return None

			val (label, _) = fresh(ast.LocalVar(DependencyAnalyzer.analysisLabelName, ast.Bool)())
			val labelNode = dependencyAnalyzer.createLabelNode(label, sourceChunks, sourceTerms)
			val smtLabel = DependencyAnalyzer.createAssumptionLabel(labelNode.map(_.id))
			assumeLabel(label, smtLabel)
			labelNode
		}

		override def wrapWithDependencyAnalysisLabel(term: Term, sourceChunks: Iterable[Chunk] = Set.empty, sourceTerms: Iterable[Term] = Set.empty): Term = {
			if (!isDependencyAnalysisEnabled || term.equals(True) || sourceChunks.size + sourceTerms.size == 0)
				return term

			val labelNode = getOrCreateAnalysisLabelNode(sourceChunks, sourceTerms)
			labelNode.map(n => Implies(n.term, term)).getOrElse(term)
		}

		override protected def assumeWithoutSmokeChecks(termsWithLabel: InsertionOrderedSet[(Term, String)], analysisInfos: DependencyAnalysisInfos, isDefinition: Boolean = false): Unit = {
			super.assumeWithoutSmokeChecks(addAssumptionLabels(termsWithLabel.map(_._1), analysisInfos), analysisInfos, isDefinition)
		}

		private def addAssumptionLabels(filteredTerms: Iterable[Term], analysisInfos: DependencyAnalysisInfos) = {
			InsertionOrderedSet(filteredTerms map (t => {
				val assumptionIds = dependencyAnalyzer.addAssumption(t, analysisInfos)
				(t, DependencyAnalyzer.createAssumptionLabel(assumptionIds))
			}))
		}

		override def checkSmoke(analysisInfos: DependencyAnalysisInfos, isAssert: Boolean=false): Boolean = {
			val checkNode = dependencyAnalyzer.createAssertOrCheckNode(False, analysisInfos, !isAssert)
			val label = DependencyAnalyzer.createAssertionLabel(checkNode.map(_.id))

			if (isPathInfeasible) {
				checkNode foreach dependencyAnalyzer.addAssertionNode
				dependencyAnalyzer.addDependency(pcs.getCurrentInfeasibilityNode, checkNode.map(_.id))
				return true
			}

			val result = super.checkSmokeInternal(isAssert, label)

			if (result) {
				checkNode foreach dependencyAnalyzer.addAssertionNode
				dependencyAnalyzer.processUnsatCoreAndAddDependencies(prover.getLastUnsatCore, label)
				val infeasibleNodeId = dependencyAnalyzer.addInfeasibilityNode(!isAssert, analysisInfos)
				dependencyAnalyzer.addDependency(checkNode.map(_.id), infeasibleNodeId)
				pcs.setCurrentInfeasibilityNode(infeasibleNodeId)
			} else if (isAssert) {
				checkNode foreach (node => dependencyAnalyzer.addAssertionNode(node.getAssertFailedNode))
			}
			result
		}

		override def handleFailedAssertion(failedAssertion: Term, e: Option[ast.Exp], finalExp: Option[ast.Exp], analysisInfos: DependencyAnalysisInfos, assumeFailedAssertion: Boolean): Unit = {
			dependencyAnalyzer.addAssertionFailedNode(failedAssertion, analysisInfos)
			super.handleFailedAssertion(failedAssertion, e, finalExp, analysisInfos, assumeFailedAssertion)
		}

		override def handleAndGetUpdatedAnalysisInfos(analysisInfos: DependencyAnalysisInfos, info: Info, node: ast.Node): DependencyAnalysisInfos = {
			val newAnalysisInfos = analysisInfos.addInfo(info, node)
			info.getAllInfos[AdditionalDependencyNodeInfo].foreach {
				case AdditionalAssertionNode() => dependencyAnalyzer.createAssertOrCheckNode(True, newAnalysisInfos, isCheck = false).foreach(n => {
					dependencyAnalyzer.addAssertionNode(n)
					if (isPathInfeasible) dependencyAnalyzer.addDependency(pcs.getCurrentInfeasibilityNode, Some(n.id))
				})
				case AdditionalAssumptionNode() => dependencyAnalyzer.addAssumption(True, newAnalysisInfos)
			}
			newAnalysisInfos
		}

		override protected def isKnownToBeTrue(t: Term) = t.equals(True)

		override protected def deciderAssertInternal(asserted: Boolean, t: Term, timeout: Option[Int], analysisInfos: DependencyAnalysisInfos, isCheck: Boolean, label: String = "") = {

			val assertNode = if (!asserted) dependencyAnalyzer.createAssertOrCheckNode(t, analysisInfos, isCheck) else None

			val label = DependencyAnalyzer.createAssertionLabel(assertNode map (_.id))

			val result: Boolean = super.deciderAssertInternal(asserted, t, timeout, analysisInfos, isCheck, label)

			if (result) {
				assertNode foreach dependencyAnalyzer.addAssertionNode
			}

			result
		}

		override protected def proverAssert(t: Term, timeout: Option[Mark], label: String): Boolean = {
			val result = super.proverAssert(t, timeout, label)
			if (isPathInfeasible)
				dependencyAnalyzer.addDependency(pcs.getCurrentInfeasibilityNode, Some(DependencyAnalyzer.getIdFromLabel(label)))
			else if (result)
				dependencyAnalyzer.processUnsatCoreAndAddDependencies(prover.getLastUnsatCore, label)
			result
		}
	}
}

class DependencyAwareMainVerifier(config: Config,
																	override val reporter: Reporter,
																	override val rootSymbExLogger: SymbExLogger[_ <: MemberSymbExLogger])
	extends DefaultMainVerifier(config, reporter, rootSymbExLogger) with DependencyAnalysisAwareVerifier {

	override def createWorkerVerifier(): DependencyAwareWorkerVerifier = new DependencyAwareWorkerVerifier(this, nextUniqueVerifierId(), reporter, debugMode)

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

	override def functionsSupporter: FunctionsSupporter = DependencyAwareFunctionSupporter

	object DependencyAwareFunctionSupporter extends FunctionsSupporter {
		override protected def handleFunction(sInit: State, function: ast.Function): VerificationResult = {

			val presAssertionNodeForJoin = function.pres.flatMap(_.topLevelConjuncts).map(pc => SimpleAssertionNode(True, AnalysisSourceInfo.createAnalysisSourceInfo(pc), AssumptionType.Precondition, SimpleDependencyAnalysisMerge(AnalysisSourceInfo.createAnalysisSourceInfo(pc)), List(SimpleDependencyAnalysisJoin(AnalysisSourceInfo.createAnalysisSourceInfo(pc), JoinType.Sink, EdgeType.Up)), function.name))
			presAssertionNodeForJoin foreach decider.dependencyAnalyzer.addAssertionNode

			val result = super.handleFunction(sInit, function)

			if (function.body.isEmpty) {
				decider.dependencyAnalyzer.addNodes(decider.prover.getPreambleAnalysisNodes)
				decider.dependencyAnalyzer.addDependenciesForAbstractMembers(function.pres.flatMap(_.topLevelConjuncts), function.posts.flatMap(_.topLevelConjuncts), DependencyAnalysisInfos.DefaultDependencyAnalysisInfos)
			}

			val allErrors = (result :: result.previous.toList).filter(_.isInstanceOf[Failure]).map(_.asInstanceOf[Failure])
			result.dependencyGraphInterpreter = decider.dependencyAnalyzer.buildFinalGraph().map(new DependencyGraphInterpreter(function.name, _,
				allErrors, Some(function)))

			result
		}

		override protected def emitAndRecordFunctionAxioms(axiom: (Term, DependencyAnalysisAxiomInfo)*): Unit = {
			val cleanAxiom =
				if (!Verifier.config.enableDependencyAnalysis()) axiom
				else axiom.map(a => (a._1.transform{
					case Var(name, _, _) if name.name.startsWith(DependencyAnalyzer.analysisLabelName) => True // replace dependency analysis labels by True to avoid errors
				}(), a._2))
			decider.prover.assumeAxiomsWithAnalysisInfo(InsertionOrderedSet(cleanAxiom), "Function axioms")

			emittedFunctionAxioms = emittedFunctionAxioms ++ cleanAxiom
		}

		override def emitAxiomsAfterVerification(sink: ProverLike): Unit = {
			sink.assumeAxiomsWithAnalysisInfo(InsertionOrderedSet(emittedFunctionAxioms), "Function axioms")
		}

	}
}

class DependencyAwareWorkerVerifier(mainVerifier: DependencyAwareMainVerifier,
																		uniqueId: String,
																		override val reporter: Reporter,
																		override val debugMode: Boolean) extends WorkerVerifier(mainVerifier, uniqueId, reporter, debugMode) with DependencyAnalysisAwareVerifier {

	override def methodSupporter: MethodSupporter = DependencyAwareMethodSupporter

	object DependencyAwareMethodSupporter extends MethodSupporter {

		override def verify(sInit: State, method: Method): Seq[VerificationResult] = {

			val presAssertionNodeForJoin = method.pres.flatMap(_.topLevelConjuncts).map(pc => SimpleAssertionNode(True, AnalysisSourceInfo.createAnalysisSourceInfo(pc), AssumptionType.Precondition, SimpleDependencyAnalysisMerge(AnalysisSourceInfo.createAnalysisSourceInfo(pc)), List(SimpleDependencyAnalysisJoin(AnalysisSourceInfo.createAnalysisSourceInfo(pc), JoinType.Sink, EdgeType.Up)), method.name))
			presAssertionNodeForJoin foreach decider.dependencyAnalyzer.addAssertionNode

			val result = super.verify(sInit, method)

			if (method.body.isEmpty)
				decider.dependencyAnalyzer.addDependenciesForAbstractMembers(method.pres.flatMap(_.topLevelConjuncts), method.posts.flatMap(_.topLevelConjuncts), DependencyAnalysisInfos.DefaultDependencyAnalysisInfos)

			result foreach (r => {
				val allErrors = (r :: r.previous.toList).filter(_.isInstanceOf[Failure]).map(_.asInstanceOf[Failure])
				r.dependencyGraphInterpreter = decider.dependencyAnalyzer.buildFinalGraph().map(new DependencyGraphInterpreter(method.name, _, allErrors, Some(method)))
			})

			result
		}
	}
}

trait DependencyAnalysisDeciderFeatures {
	def registerChunk[CH <: GeneralChunk](buildChunk: Term => CH, perm: Term, analysisInfos: DependencyAnalysisInfos, isExhale: Boolean): CH

	def registerDerivedChunk[CH <: GeneralChunk](sourceChunks: Set[Chunk], buildChunk: Term => CH, perm: Term, analysisInfos: DependencyAnalysisInfos, isExhale: Boolean, createLabel: Boolean = true): CH

	def initDependencyAnalyzer(member: Member, preambleNodes: Iterable[DependencyAnalysisNode]): Unit
	def resetDependencyAnalyzer(): Unit

}