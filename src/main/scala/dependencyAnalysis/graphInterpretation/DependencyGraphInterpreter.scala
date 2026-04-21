package viper.silicon.dependencyAnalysis.graphInterpretation

import dependencyAnalysis.UserLevelDependencyAnalysisNode
import viper.silicon.dependencyAnalysis._
import viper.silicon.interfaces.Failure
import viper.silicon.verifier.Verifier
import viper.silver.ast
import viper.silver.ast.Program
import viper.silver.dependencyAnalysis.{AbstractDependencyGraphInterpreter, AssumptionType, JoinType}

import java.io.PrintWriter
import java.nio.file.Paths

object DATraversalMode extends Enumeration {
  type DATraversalMode = Value
  val Upwards, Downwards = Value
}

class DependencyGraphInterpreter[T <: DependencyGraphState](name: String, dependencyGraph: ReadOnlyDependencyGraph[T], errors: List[Failure], member: Option[ast.Member]=None) extends AbstractDependencyGraphInterpreter {
	val pruningSupporter: DependencyAnalysisPruningSupporter[T] = new DependencyAnalysisPruningSupporter[T](this)
	val progressSupporter: DependencyAnalysisProgressSupporter[T] = new DependencyAnalysisProgressSupporter[T](this)


	def getGraph: ReadOnlyDependencyGraph[T] = dependencyGraph

	def getName: String = name

	def getMember: Option[ast.Member] = member

	lazy val nodesMap: Map[Int, DependencyAnalysisNode] = getNodes.map(node => (node.id, node)).toMap
	lazy val nonInternalAssumptionNodesMap: Map[Int, DependencyAnalysisNode] = getNonInternalAssumptionNodes(getNodes).map(node => (node.id, node)).toMap
	lazy val assertionNodesMap: Map[Int, DependencyAnalysisNode] = getAssertionNodes.map(node => (node.id, node)).toMap

	def getNodes: Set[DependencyAnalysisNode] = dependencyGraph.getNodes.toSet

	def getAssumptionNodes: Set[DependencyAnalysisNode] = dependencyGraph.getAssumptionNodes.toSet

	def getAssertionNodes: Set[DependencyAnalysisNode] = dependencyGraph.getAssertionNodes.toSet

	def getErrors: List[Failure] = errors

	// TODO ake: join nodes are not needed for the final graph. Maybe we can outsource this to a dedicated intraprocedural graph interpreter class.
	val joinSinkNodes: Set[DependencyAnalysisNode] = getJoinCandidateNodes(getNodes).filter(_.joinInfos.exists(_.joinType.equals(JoinType.Sink)))
	val joinSourceNodes: Set[DependencyAnalysisNode] = getJoinCandidateNodes(getNodes).filter(_.joinInfos.exists(_.joinType.equals(JoinType.Source)))

	private def getJoinCandidateNodes(nodes: Set[DependencyAnalysisNode]): Set[DependencyAnalysisNode] = nodes.filter(node => node.joinInfos.nonEmpty)

	def toUserLevelNodes(nodes: Iterable[DependencyAnalysisNode]): Set[UserLevelDependencyAnalysisNode] = UserLevelDependencyAnalysisNode.from(nodes)

	def getNodesByLine(line: Int): Set[DependencyAnalysisNode] =
		getNodes.filter(n => !AssumptionType.internalTypes.contains(n.assumptionType)).filter(node => node.sourceInfo.getLineNumber.isDefined && node.sourceInfo.getLineNumber.get == line)

	def getNodesByPosition(file: String, line: Int): Set[DependencyAnalysisNode] =
		getNodes.filter(n => !AssumptionType.internalTypes.contains(n.assumptionType)).filter(node => node.sourceInfo.getLineNumber.isDefined && node.sourceInfo.getLineNumber.get == line && node.sourceInfo.getPositionString.startsWith(file + "."))


	def getNodesByLabel(label: String): Set[DependencyAnalysisNode] = {
		val fullAnnotation = ("""@label\(\s*"?""" + java.util.regex.Pattern.quote(label) + """"?\s*\)""").r
		getNodes.filter(node => fullAnnotation.findFirstIn(node.toString).isDefined)
	}

	def getDirectDependencies(nodeIdsToAnalyze: Set[Int]): Set[DependencyAnalysisNode] = {
		var queue = nodeIdsToAnalyze
		var result: Set[Int] = Set.empty
		val internalNodeIds = getAssumptionNodes.diff(getNonInternalAssumptionNodes).map(_.id).union(getAssertionNodes.map(_.id))
		while (queue.nonEmpty) {
			val directDependencyIds = queue flatMap (id => dependencyGraph.getDirectEdges.getOrElse(id, Set.empty))
			queue = internalNodeIds.intersect(directDependencyIds).diff(result) // internal assumptions are hidden -> add their direct dependencies instead
			result = result.union(directDependencyIds)
		}

		getNonInternalAssumptionNodes.filter(node => result.contains(node.id))
	}

	private def getAllDependencies(nodeIdsToAnalyze: Set[Int], includeInfeasibilityNodes: Boolean = true) = {
		val allDependenciesUpwards = dependencyGraph.getAllDependencies(nodeIdsToAnalyze, includeInfeasibilityNodes, includeUpwardEdges = true, includeDownwardEdges = false)
		val allDependenciesDownwards = dependencyGraph.getAllDependencies(nodeIdsToAnalyze ++ allDependenciesUpwards, includeInfeasibilityNodes, includeUpwardEdges = false, includeDownwardEdges = true)
		allDependenciesUpwards ++ allDependenciesDownwards
	}

	def getAllNonInternalDependencies(nodeIdsToAnalyze: Set[Int], includeInfeasibilityNodes: Boolean = true): Set[DependencyAnalysisNode] = {
		getAllDependencies(nodeIdsToAnalyze, includeInfeasibilityNodes) flatMap nonInternalAssumptionNodesMap.get
	}

	def getAllExplicitDependencies(nodeIdsToAnalyze: Set[Int], includeInfeasibilityNodes: Boolean = true): Set[DependencyAnalysisNode] = {
		val allDeps = getAllDependencies(nodeIdsToAnalyze, includeInfeasibilityNodes)
		getExplicitAssumptionNodes.filter(node => allDeps.contains(node.id))
	}

	private def getAllDependents(nodeIdsToAnalyze: Set[Int], includeInfeasibilityNodes: Boolean = true) = {
		val allDependentsDownwards = dependencyGraph.getAllDependents(nodeIdsToAnalyze, includeInfeasibilityNodes, includeUpwardEdges = false, includeDownwardEdges = true)
		val allDependentsUpwards = dependencyGraph.getAllDependents(nodeIdsToAnalyze ++ allDependentsDownwards, includeInfeasibilityNodes, includeUpwardEdges = true, includeDownwardEdges = false)
		allDependentsUpwards ++ allDependentsDownwards
	}

	def getAllNonInternalDependents(nodeIdsToAnalyze: Set[Int], includeInfeasibilityNodes: Boolean = true): Set[DependencyAnalysisNode] = {
		val allDeps = getAllDependents(nodeIdsToAnalyze, includeInfeasibilityNodes)
		getNonInternalAssertionNodes.filter(node => allDeps.contains(node.id))
	}

	def getAllExplicitDependents(nodeIdsToAnalyze: Set[Int], includeInfeasibilityNodes: Boolean = true): Set[DependencyAnalysisNode] = {
		val allDeps = getAllDependents(nodeIdsToAnalyze, includeInfeasibilityNodes)
		getExplicitAssertionNodes.filter(node => allDeps.contains(node.id))
	}

	def getNonInternalAssumptionNodes: Set[DependencyAnalysisNode] = nonInternalAssumptionNodesMap.values.toSet

	def getNonInternalAssumptionNodes(nodes: Set[DependencyAnalysisNode]): Set[DependencyAnalysisNode] = nodes filter (node =>
		(node.isInstanceOf[GeneralAssumptionNode] && !AssumptionType.internalTypes.contains(node.assumptionType))
			|| AssumptionType.postconditionTypes.contains(node.assumptionType) || node.joinInfos.nonEmpty // TODO ake: find a better way to include the join nodes
		)

	def getExplicitAssumptionNodes: Set[DependencyAnalysisNode] = getNonInternalAssumptionNodes filter (node =>
		AssumptionType.explicitAssumptionTypes.contains(node.assumptionType)
		)

	def getNonInternalAssertionNodes: Set[DependencyAnalysisNode] = getAssertionNodes filter (node =>
		!AssumptionType.internalTypes.contains(node.assumptionType) || node.joinInfos.nonEmpty)

	def getExplicitAssertionNodes: Set[DependencyAnalysisNode] =
		getNonInternalAssertionNodes.filter(node => AssumptionType.explicitAssertionTypes.contains(node.assumptionType))

	def getAssertionNodesWithFailures: Set[GeneralAssertionNode] =
		getNonInternalAssertionNodes.filter(_.isInstanceOf[GeneralAssertionNode]).map(_.asInstanceOf[GeneralAssertionNode]).filter(_.hasFailed)

	def exportGraph(program: ast.Program): Unit = {
		if (Verifier.config.dependencyAnalysisExportPath.isEmpty) return
		val directory = Paths.get(Verifier.config.dependencyAnalysisExportPath()).toFile
		directory.mkdir()
		dependencyGraph.exportGraph(Verifier.config.dependencyAnalysisExportPath() + "/" + name)
		exportProgram(program, Verifier.config.dependencyAnalysisExportPath() + "/" + name)
	}

	private def exportProgram(program: Program, path: String): Unit = {
		// TODO ake: we should copy the original source file in order to keep the line numbering!
		val writer = new PrintWriter(path + "/program.vpr")
		writer.println(program.toString())
		writer.close()
	}

	private def getNodesWithIdenticalSource(nodes: Set[DependencyAnalysisNode]): Set[DependencyAnalysisNode] = {
		val sourceInfos = nodes map (_.sourceInfo)
		getNodes filter (node => sourceInfos.contains(node.sourceInfo))
	}

	// TODO ake: might be deprecated
	def computeProofCoverage(): (Double, Set[String]) = {
		val explicitAssertionNodes = getNodesWithIdenticalSource(getExplicitAssertionNodes)
		computeProofCoverage(explicitAssertionNodes)
	}

	// TODO ake: might be deprecated
	def computeProofCoverage(assertionNodes: Set[DependencyAnalysisNode]): (Double, Set[String]) = {
		val assertionNodeIds = assertionNodes map (_.id)
		val dependencies = dependencyGraph.getAllDependencies(assertionNodeIds, includeInfeasibilityNodes = true, includeUpwardEdges = true, includeDownwardEdges = true)
		val coveredNodes = dependencies ++ assertionNodeIds

		val userLevelNodes = toUserLevelNodes(getNonInternalAssumptionNodes.filterNot(_.isInstanceOf[AxiomAssumptionNode]))
		if (userLevelNodes.isEmpty) return (Double.NaN, Set())

		val uncoveredUserLevelNodes = userLevelNodes filter (node =>
			coveredNodes.intersect(node.lowerLevelNodes.map(_.id)).isEmpty
			)
		val proofCoverage = 1.0 - (uncoveredUserLevelNodes.size.toDouble / userLevelNodes.size.toDouble)
		(proofCoverage, uncoveredUserLevelNodes.map(_.toString))
	}
}


