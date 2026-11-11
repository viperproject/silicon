// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silicon.dependencyAnalysis

import com.typesafe.scalalogging.LazyLogging
import viper.silicon.dependencyAnalysis.graph._
import viper.silicon.state.chunks.{Chunk, GeneralChunk}
import viper.silicon.state.terms.{NoPerm, _}
import viper.silver.ast
import viper.silver.ast._
import viper.silver.dependencyAnalysis._

import scala.collection.mutable


trait DependencyAnalyzer {
  protected val dependencyGraph: DependencyGraph[Init] = new DependencyGraph()

  def getMember: ast.Member

  /**
   * Replaces the axiom nodes considered when finalizing the graph.
   * Needed for axioms that are emitted while the member is verified and that the member's graph must take into account.
   */
  def setAxiomNodes(axiomNodes: AxiomNodes): Unit

  def addAssertionNode(node: GeneralAssertionNode): Unit
  def addAssumptionNode(node: GeneralAssumptionNode): Unit
  def addAssumption(assumption: Term, analysisInfos: AnalysisInfos, description: Option[String] = None): Option[Int]
  def registerInhaleChunk[CH <: GeneralChunk](buildChunk: Term => CH, perm: Term, labelNode: Option[LabelNode], analysisInfos: AnalysisInfos): CH = buildChunk(perm)
  def registerExhaleChunk[CH <: GeneralChunk](buildChunk: Term => CH, perm: Term, labelNodeOpt: Option[LabelNode], analysisInfos: AnalysisInfos): CH = buildChunk(perm)
  def createLabelNode(label: Var, sourceNodeId: Option[Int]): Option[LabelNode]

  def createAssertOrCheckNode(term: Term, analysisInfos: AnalysisInfos, isCheck: Boolean): Option[GeneralAssertionNode]
  def addAssertFalseNode(isCheck: Boolean, analysisInfos: AnalysisInfos): Option[Int]
  def addInfeasibilityNode(isCheck: Boolean, analysisInfos: AnalysisInfos): Option[Int]
  def addAssertionFailedNode(failedAssertion: Term, analysisInfos: AnalysisInfos): Option[Int]

  /**
   * Adds a dependency between all pairs of source and dest node ids.
   */
  def addDependency(source: Option[Int], dest: Option[Int]): Unit

  /**
   * @param unsatCore The labels in the UNSAT core as reported by Z3.
   * @param assertionId the id of the assertion that was proven using the UNSAT core
   *
   *  Adds all components of the UNSAT core as dependencies of the provided assertion.
   */
  def processUnsatCoreAndAddDependencies(unsatCore: Seq[String], assertionId: Int): Unit

  /**
   * Adds dependencies between all pairs of sourceExps and targetExps, where sourceExps should be preconditions and
   * targetExps should be postconditions of an abstract function or method.
   */
  def addDependenciesForAbstractMembers(sourceExps: Seq[ast.Exp], targetExps: Seq[ast.Exp], analysisInfos: AnalysisInfos): Unit

  /**
   * Adds an assertion and assumption node with the given analysis source info including dependencies to the current infeasibility node.
   */
  def addAssertionWithDepToInfeasNode(infeasNodeId: Option[Int], analysisInfos: AnalysisInfos): Unit = {}

  /**
   * @return the final dependency graph representing all (direct and transitive) intraprocedural dependencies
   */
  def buildFinalGraph(): Option[DependencyGraph[IntraProcedural]]

  /**
   * Stores the information that all nodes having a merge info in sourceExps should be connected to all nodes having a
   * merge info in targetExps.
   * These edges are eventually added when building the final graph ([[viper.silicon.dependencyAnalysis.DependencyAnalyzer#buildFinalGraph]]).
   */
  def addCustomDependenciesBetweenMergeInfos(sourceExps: Seq[Exp], targetExps: Seq[Exp]): Unit
}

object DependencyAnalyzer extends LazyLogging {
  val analysisLabelName: String = "$$analysisLabel$$"
  private val assumptionLabelPrefix = "assumption"
  private val assertionLabelPrefix = "assertion"
  private val axiomLabelPrefix = "axiom"

  private def extractAnnotationFromInfo(info: ast.Info, annotationKey: String): Option[Seq[String]] = {
    info.getAllInfos[ast.AnnotationInfo]
      .filter(_.values.contains(annotationKey))
      .map(_.values(annotationKey)).headOption
  }

  /** Every node is built from infos that passed through here, so that incomplete infos are reported. */
  def checkedInfos(analysisInfos: AnalysisInfos, memberName: String, options: DependencyAnalysisOptions): AnalysisInfos = {
    val missingInfos = analysisInfos.missingInfos
    if (missingInfos.nonEmpty) {
      val message = s"Dependency analysis results might be unsound because of incomplete infos in member $memberName: ${missingInfos.mkString("; ")}"
      if (options.enableDebugging) sys.error(message) else logger.warn(message)
    }
    analysisInfos
  }

  def extractEnableAnalysisFromInfo(info: ast.Info): Option[Boolean] = {
    val annotation = extractAnnotationFromInfo(info, DependencyAnalysisAnnotations.enableDependencyAnalysisKey)
    if (annotation.isDefined && annotation.get.nonEmpty) annotation.get.head.toBooleanOption else None
  }

  def createAssumptionLabel(id: Option[Int]): Option[String] = {
    createLabel(assumptionLabelPrefix, id)
  }

  def createAssertionLabel(id: Option[Int]): Option[String] = {
    createLabel(assertionLabelPrefix, id)
  }

  def createAxiomLabel(id: Option[Int]): Option[String] = {
    createLabel(axiomLabelPrefix, id)
  }

  private def createLabel(description: String, id: Option[Int]): Option[String] = {
    id.map(description + "_" + _)
  }

  def isAnalysisLabel(v: Var): Boolean = v.id.name.startsWith(analysisLabelName)

  private lazy val labelPrefixes = Seq(assumptionLabelPrefix, assertionLabelPrefix, axiomLabelPrefix)
  def getIdFromLabel(label: String): Option[Int] = {
    val parts = label.split("_")
    if (labelPrefixes.exists(parts(0).startsWith))
      parts(1).toIntOption
    else
      None
  }
}

class DefaultDependencyAnalyzer(member: ast.Member, options: DependencyAnalysisOptions, private var axiomNodes: AxiomNodes) extends DependencyAnalyzer {
  protected var customMergeDependencies: Set[(Set[DependencyAnalysisMergeInfo], Set[DependencyAnalysisMergeInfo])] = Set.empty

  override def getMember: ast.Member = member

  private def checked(analysisInfos: AnalysisInfos): AnalysisInfos =
    DependencyAnalyzer.checkedInfos(analysisInfos, member.name, options)

  private def assumptionMetadata(analysisInfos: AnalysisInfos): NodeMetadata = NodeMetadata.forAssumption(checked(analysisInfos), getMember.name)

  private def assertionMetadata(analysisInfos: AnalysisInfos): NodeMetadata = NodeMetadata.forAssertion(checked(analysisInfos), getMember.name)

  override def setAxiomNodes(axiomNodes: AxiomNodes): Unit = {
    this.axiomNodes = axiomNodes
  }

  override def addAssumptionNode(node: GeneralAssumptionNode): Unit =
    dependencyGraph.addAssumptionNode(node)

  override def addAssertionNode(node: GeneralAssertionNode): Unit = dependencyGraph.addAssertionNode(node)

  override def addAssumption(assumption: Term, analysisInfos: AnalysisInfos, description: Option[String]): Option[Int] = {
    val node = DependencyNodeFactory.createSimpleAssumptionNode(assumption, description, assumptionMetadata(analysisInfos))
    addAssumptionNode(node)
    Some(node.id)
  }

  override def registerExhaleChunk[CH <: GeneralChunk](buildChunk: Term => CH, perm: Term, labelNodeOpt: Option[LabelNode], analysisInfos: AnalysisInfos): CH = {
    val labelNode = labelNodeOpt.get
    val chunk = buildChunk(Ite(labelNode.term, perm, NoPerm))
    val chunkNode = addPermissionExhaleNode(chunk, chunk.perm, analysisInfos, labelNode)
    if (chunkNode.isDefined) addDependency(chunkNode, Some(labelNode.id))
    chunk
  }

  override def registerInhaleChunk[CH <: GeneralChunk](buildChunk: Term => CH, perm: Term, labelNodeOpt: Option[LabelNode], analysisInfos: AnalysisInfos): CH = {
    val labelNode = labelNodeOpt.get
    val chunk = buildChunk(Ite((labelNode.term, perm, NoPerm)))
    val chunkNode = addPermissionInhaleNode(chunk, chunk.perm, analysisInfos, labelNode)
    if (chunkNode.isDefined) addDependency(chunkNode, Some(labelNode.id))
    chunk
  }

  private def addPermissionInhaleNode(chunk: Chunk, permAmount: Term, analysisInfos: AnalysisInfos, labelNode: LabelNode): Option[Int] = {
    val node = DependencyNodeFactory.createPermissionInhaleNode(chunk, permAmount, assumptionMetadata(analysisInfos), labelNode)
    addAssumptionNode(node)
    Some(node.id)
  }

  private def addPermissionExhaleNode(chunk: Chunk, permAmount: Term, analysisInfos: AnalysisInfos, labelNode: LabelNode): Option[Int] = {
    val node = DependencyNodeFactory.createPermissionExhaleNode(chunk, permAmount, assertionMetadata(analysisInfos), labelNode)
    addAssertionNode(node)
    Some(node.id)
  }

  override def createLabelNode(label: Var, sourceNodeId: Option[Int]): Option[LabelNode] = {
    val labelNode = DependencyNodeFactory.createLabelNode(label, getMember.name)
    addAssumptionNode(labelNode)
    dependencyGraph.addEdges(sourceNodeId.toSet, labelNode.id)
    Some(labelNode)
  }

  override def createAssertOrCheckNode(term: Term, analysisInfos: AnalysisInfos, isCheck: Boolean): Option[GeneralAssertionNode] = {
    val metadata = assertionMetadata(analysisInfos)
    if (isCheck) Some(DependencyNodeFactory.createSimpleCheckNode(term, metadata))
    else Some(DependencyNodeFactory.createSimpleAssertionNode(term, metadata))
  }
  
  private def addAssertNode(term: Term, analysisInfos: AnalysisInfos): Option[Int] = {
    val node = createAssertOrCheckNode(term, analysisInfos, isCheck=false)
    node foreach addAssertionNode
    node map (_.id)
  }

  override def addAssertFalseNode(isCheck: Boolean, analysisInfos: AnalysisInfos): Option[Int] = {
    val node = createAssertOrCheckNode(False, analysisInfos, isCheck)
    addAssertionNode(node.get)
    node.map(_.id)
  }

  override def addInfeasibilityNode(isCheck: Boolean, analysisInfos: AnalysisInfos): Option[Int] = {
    checked(analysisInfos)
    val node = DependencyNodeFactory.createInfeasibilityNode(analysisInfos.getSourceInfo, analysisInfos.getDependencyType.assumptionType, getMember.name)
    addAssumptionNode(node)
    Some(node.id)
  }

  override def addAssertionFailedNode(failedAssertion: Term, analysisInfos: AnalysisInfos): Option[Int] = {
    val assumeNode = DependencyNodeFactory.createSimpleAssumptionNode(failedAssertion, None, assumptionMetadata(analysisInfos).copy(originType = analysisInfos.getDependencyType.assertionType))
    val assertFailedNode = DependencyNodeFactory.createSimpleAssertionNode(failedAssertion, assertionMetadata(analysisInfos), hasFailed=true)
    dependencyGraph.addNode(assumeNode)
    dependencyGraph.addNode(assertFailedNode)
    dependencyGraph.addEdges(Set(assumeNode.id), assertFailedNode.id)
    Some(assertFailedNode.id)
  }


  override def addDependency(source: Option[Int], dest: Option[Int]): Unit = {
    if (source.isDefined && dest.isDefined)
      dependencyGraph.addEdges(source.get, Set(dest.get))
  }

  override def processUnsatCoreAndAddDependencies(unsatCore: Seq[String], assertionId: Int): Unit = {
    val assumptionIds = unsatCore.flatMap(DependencyAnalyzer.getIdFromLabel).toSet
    // TODO ake: collect vacuous proof information
    // if (!assumptionIds.contains(assertionId))
    //   dependencyGraph.addVacuousProof(assertionId)
    dependencyGraph.addEdges(assumptionIds.diff(Set(assertionId)), assertionId)
  }

  override def addDependenciesForAbstractMembers(sourceExps: Seq[ast.Exp], targetExps: Seq[ast.Exp], analysisInfos: AnalysisInfos): Unit = {
    val sourceNodeIds = sourceExps.flatMap(e => addAssumption(True, analysisInfos.addInfo(e.info, e).withJoinInfo(EvalStackDependencyAnalysisJoin(JoinType.Sink, EdgeType.Up))))
    val targetNodes = targetExps.flatMap(e => addAssertNode(True, analysisInfos.addInfo(e.info, e).withJoinInfo(EvalStackDependencyAnalysisJoin(JoinType.Source, EdgeType.Down))))
    dependencyGraph.addEdges(sourceNodeIds.toSet, targetNodes.toSet)
  }

  override def addCustomDependenciesBetweenMergeInfos(sourceExps: Seq[Exp], targetExps: Seq[Exp]): Unit = {
    val sourceMergeInfos = sourceExps.flatMap(_.info.getUniqueInfo[DependencyAnalysisMergeInfo]).filter(_.isMerge).toSet
    val targetMergeInfos = targetExps.flatMap(_.info.getUniqueInfo[DependencyAnalysisMergeInfo]).filter(_.isMerge).toSet

    customMergeDependencies = Set((sourceMergeInfos, targetMergeInfos)) ++ customMergeDependencies
  }

  protected def addCustomMergeDependencies(mergedGraph: DependencyGraph[IntraProcedural]): Unit = {
    def nodeIdsWithMergeInfos(mergeInfos: Set[DependencyAnalysisMergeInfo]): Set[Int] =
      mergedGraph.getNodes.filter(node => mergeInfos.contains(node.mergeInfo)).map(_.id) ++ mergeInfos.flatMap(axiomNodes.idsWithMergeInfo)

    customMergeDependencies.foreach{ case (sourceMergeInfos, targetMergeInfos) =>
      mergedGraph.addEdges(nodeIdsWithMergeInfos(sourceMergeInfos), nodeIdsWithMergeInfos(targetMergeInfos))
    }
  }

  /**
   *
   * @return the final dependency graph
   * This operation ensures sound computation of transitive dependencies by adding edges between nodes originating from the same
   * source code statement.
   * Further, this operation removes unnecessary details from the graph by, for example, removing label nodes and merging identical nodes.
   */
  override def buildFinalGraph(): Option[DependencyGraph[IntraProcedural]] = {
    dependencyGraph.removeLabelNodes()
    val mergedGraph = if (options.enableDebugging) dependencyGraph.asInstanceOf[DependencyGraph[IntraProcedural]] else buildAndGetMergedGraph()
    addTransitiveEdges(mergedGraph)
    if (!options.enableDebugging) mergedGraph.removeInternalNodes(axiomNodes.isRemovableInternalNode)
    Some(mergedGraph)
  }

  /**
   * Adds edges between the nodes with identical merge info and the ones to be connected as given by the custom merge dependencies
   * to the merged graph. This step is necessary to ensure that the low-level graph is connected and encodes all direct
   * and indirect dependencies.
   */
  private def addTransitiveEdges(mergedGraph: DependencyGraph[IntraProcedural]): Unit = {
    val nodesPerSourceInfo = mergedGraph.getNodes.filter(_.mergeInfo.isMerge).groupBy(_.mergeInfo)
    nodesPerSourceInfo foreach {case (mergeInfo, nodes) =>
      val axiomIds = axiomNodes.idsWithMergeInfo(mergeInfo)
      val asserts = nodes.collect { case n: GeneralAssertionNode => n }
      val assumes = nodes.filter {
        case _: LabelNode => false
        case _: GeneralAssumptionNode => true
        case _ => false
      }
      mergedGraph.addEdges(asserts.map(_.id), assumes.map(_.id) ++ axiomIds)
      val checks = nodes.collect { case n: SimpleCheckNode => n }
      val notChecks = nodes.filter {
        case _: SimpleCheckNode => false
        case _ => true
      }
      mergedGraph.addEdges(checks.map(_.id), notChecks.map(_.id) ++ axiomIds) // TODO ake: why do we need this?
    }

    addCustomMergeDependencies(mergedGraph)
  }

  /**
   * Creates a new graph where nodes that only differ in irrelevant information are merged into one node.
   * As a result, this operation removes some lower-level details from the graph.
   * This step can be skipped for debugging purposes by setting the enableDependencyAnalysisDebugging flag. Doing so
   * has no effect on the dependency results but allows to inspect low-level details while debugging and exporting
   * the low-level graph containing all details.
   */
  private def buildAndGetMergedGraph(): DependencyGraph[IntraProcedural] = {
    def keepNode(n: DependencyAnalysisNode): Boolean = n match {
      case _: InfeasibilityNode | _: AxiomAssumptionNode => true
      case _ => !n.mergeInfo.isMerge || n.joinInfos.nonEmpty
    }

    val mergedGraph = new DependencyGraph[IntraProcedural]
    val nodeMap = mutable.HashMap[Int, Int]()

    dependencyGraph.getAssumptionNodes.filter(keepNode).foreach { n =>
      nodeMap.put(n.id, n.id)
      mergedGraph.addAssumptionNode(n)
    }
    val assumptionNodesBySource = dependencyGraph.getAssumptionNodes.filter(!keepNode(_)).groupBy(_.metadata)
    assumptionNodesBySource foreach { case (metadata, assumptionNodes) =>
      if (assumptionNodes.nonEmpty) {
        val newNode = DependencyNodeFactory.createSimpleAssumptionNode(True, None, metadata)
        assumptionNodes foreach (n => nodeMap.put(n.id, newNode.id))
        mergedGraph.addAssumptionNode(newNode)
      }
    }

    dependencyGraph.getAssertionNodes.filter(keepNode).foreach { n =>
      nodeMap.put(n.id, n.id)
      mergedGraph.addAssertionNode(n)
    }
    val assertionNodesBySource = dependencyGraph.getAssertionNodes.filter(!keepNode(_)).groupBy(_.metadata)
    assertionNodesBySource foreach { case (metadata, assertionNodes) =>
      if (assertionNodes.nonEmpty) {
        val newNode = DependencyNodeFactory.createSimpleAssertionNode(True, metadata, hasFailed=assertionNodes.exists(_.hasFailed))
        assertionNodes foreach (n => nodeMap.put(n.id, newNode.id))
        mergedGraph.addAssertionNode(newNode)
      }
    }

    dependencyGraph.getAllEdges foreach { case (target, deps) =>
      val newTarget = nodeMap.getOrElse(target, target)
      mergedGraph.addEdges(deps.map(d => nodeMap.getOrElse(d, d)), newTarget)
    }

    mergedGraph
  }

  /**
   * Adds an assertion node with the given analysis source info and dependencies to the current infeasibility node.
   * The resulting assertion node is required to detect dependencies of the source statement/expression on infeasible paths.
   */
  override def addAssertionWithDepToInfeasNode(infeasNodeId: Option[Int], analysisInfos: AnalysisInfos): Unit = {
    val newAssertionNodeId = addAssertNode(False, analysisInfos)
    addDependency(infeasNodeId, newAssertionNodeId)
  }
}

/**
 * This DependencyAnalyzer implementation is used by default and does nothing.
 */
class NoDependencyAnalyzer extends DependencyAnalyzer {

  override def getMember: ast.Member = ast.Method("none", Seq.empty, Seq.empty, Seq.empty, Seq.empty, None)()

  override def setAxiomNodes(axiomNodes: AxiomNodes): Unit = {}
  override def addAssertionNode(node: GeneralAssertionNode): Unit = {}
  override def addAssumptionNode(node: GeneralAssumptionNode): Unit = {}
  override def addAssumption(assumption: Term, analysisInfos: AnalysisInfos, description: Option[String] = None): Option[Int] = None
  override def createLabelNode(labelTerm: Var, sourceNodeId: Option[Int]): Option[LabelNode] = None

  override def createAssertOrCheckNode(term: Term, analysisInfos: AnalysisInfos, isCheck: Boolean): Option[GeneralAssertionNode] = None
  override def addAssertFalseNode(isCheck: Boolean, analysisInfos: AnalysisInfos): Option[Int] = None
  override def addInfeasibilityNode(isCheck: Boolean, analysisInfos: AnalysisInfos): Option[Int] = None
  override def addAssertionFailedNode(failedAssertion: Term, analysisInfos: AnalysisInfos): Option[Int] = None

  override def addDependency(source: Option[Int], dest: Option[Int]): Unit = {}
  override def processUnsatCoreAndAddDependencies(unsatCore: Seq[String], assertionId: Int): Unit = {}
  override def addDependenciesForAbstractMembers(sourceExps: Seq[ast.Exp], targetExps: Seq[ast.Exp], analysisInfos: AnalysisInfos): Unit = {}

  override def buildFinalGraph(): Option[DependencyGraph[IntraProcedural]] = None

  override def addCustomDependenciesBetweenMergeInfos(sourceExps: Seq[Exp], targetExps: Seq[Exp]): Unit = {}

}
