// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silicon.dependencyAnalysis

import viper.silicon.decider.{Decider, DependencyAnalysisDeciderFeatures}
import viper.silicon.dependencyAnalysis.graphInterpretation.DependencyGraphInterpreter
import viper.silicon.state.chunks.{Chunk, GeneralChunk}
import viper.silicon.state.terms.{Implies, NoPerm, _}
import viper.silicon.verifier.Verifier
import viper.silver.ast
import viper.silver.ast._
import viper.silver.dependencyAnalysis.JoinType.JoinType
import viper.silver.dependencyAnalysis._

import scala.collection.mutable


trait DependencyAnalyzer {
  protected val dependencyGraph: DependencyGraph[Init] = new DependencyGraph()

  def getMember: ast.Member

  def getNodes: Iterable[DependencyAnalysisNode]

  def addNodes(nodes: Iterable[DependencyAnalysisNode]): Unit
  def addAssertionNode(node: GeneralAssertionNode): Unit
  def addAssumptionNode(node: GeneralAssumptionNode): Unit
  def addAssumption(assumption: Term, analysisInfos: DependencyAnalysisInfos, description: Option[String] = None): Option[Int]
  def addAxiom(assumption: Term, analysisAxiomInfo: DependencyAnalysisAxiomInfo, description: Option[String] = None): Option[Int]
  def registerInhaleChunk[CH <: GeneralChunk](sourceChunks: Set[Chunk], buildChunk: Term => CH, perm: Term, labelNode: Option[LabelNode], analysisInfos: DependencyAnalysisInfos): CH = buildChunk(perm)
  def registerExhaleChunk[CH <: GeneralChunk](sourceChunks: Set[Chunk], buildChunk: Term => CH, perm: Term, labelNodeOpt: Option[LabelNode], analysisInfos: DependencyAnalysisInfos): CH = buildChunk(perm)
  def createLabelNode(label: Var, sourceChunks: Iterable[Chunk], sourceTerms: Iterable[Term]): Option[LabelNode]

  def createAssertOrCheckNode(term: Term, analysisInfos: DependencyAnalysisInfos, isCheck: Boolean): Option[GeneralAssertionNode]
  def addAssertFalseNode(isCheck: Boolean, analysisInfos: DependencyAnalysisInfos): Option[Int]
  def addInfeasibilityNode(isCheck: Boolean, analysisInfos: DependencyAnalysisInfos): Option[Int]
  def addAssertionFailedNode(failedAssertion: Term, analysisInfos: DependencyAnalysisInfos): Option[Int]

  /**
   * Adds a dependency between all pairs of source and dest node ids.
   */
  def addDependency(source: Option[Int], dest: Option[Int]): Unit

  /**
   * @param dep The UNSAT core as reported by Z3.
   * @param assertionLabel the label of the assertion that was proven using the UNSAT core
   *
   *  Parses the UNSAT core and adds all its components as dependencies of the provided assertion.
   */
  def processUnsatCoreAndAddDependencies(dep: String, assertionLabel: String): Unit

  /**
   * Adds dependencies between all pairs of sourceExps and targetExps, where sourceExps should be preconditions and
   * targetExps should be postconditions of an abstract function or method.
   */
  def addDependenciesForAbstractMembers(sourceExps: Seq[ast.Exp], targetExps: Seq[ast.Exp], analysisInfos: DependencyAnalysisInfos): Unit

  /**
   * Adds an assertion and assumption node with the given analysis source info including dependencies to the current infeasibility node.
   */
  def addAssertionWithDepToInfeasNode(infeasNodeId: Option[Int], analysisInfos: DependencyAnalysisInfos): Unit = {}

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

object DependencyAnalyzer {
  val analysisLabelName: String = "$$analysisLabel$$"
  private val enableDependencyAnalysisAnnotationKey = "enableDependencyAnalysis"

  private def extractAnnotationFromInfo(info: ast.Info, annotationKey: String): Option[Seq[String]] = {
    info.getAllInfos[ast.AnnotationInfo]
      .filter(_.values.contains(annotationKey))
      .map(_.values(annotationKey)).headOption
  }

  def extractEnableAnalysisFromInfo(info: ast.Info): Option[Boolean] = {
    val annotation = extractAnnotationFromInfo(info, enableDependencyAnalysisAnnotationKey)
    if (annotation.isDefined && annotation.get.nonEmpty) annotation.get.head.toBooleanOption else None
  }

  def createAssumptionLabel(id: Option[Int]): String = {
    createLabel("assumption", id)
  }

  def createAssertionLabel(id: Option[Int]): String = {
    createLabel("assertion", id)
  }

  def createAxiomLabel(id: Option[Int]): String = {
    createLabel("axiom", id)
  }

  private def createLabel(description: String, id: Option[Int]): String = {
    if (id.isDefined) description + "_" + id.get
    else ""
  }

  def getIdFromLabel(label: String): Int = {
    label.split("_")(1).toInt
  }

  def addAssumption(decider: Decider, assumption: Term, analysisInfos: DependencyAnalysisInfos, description: Option[String] = None): Option[Int] = decider match {
    case daDecider: DependencyAnalysisDeciderFeatures => daDecider.getDependencyAnalyzer.addAssumption(assumption, analysisInfos, description)
    case _ => None
  }

  def addCustomDependenciesBetweenMergeInfos(decider: Decider, sourceExps: Seq[Exp], targetExps: Seq[Exp]): Unit = decider match {
    case daDecider: DependencyAnalysisDeciderFeatures => daDecider.getDependencyAnalyzer.addCustomDependenciesBetweenMergeInfos(sourceExps, targetExps)
    case _ =>
  }


  def wrapWithDependencyAnalysisLabel(decider: Decider, term: Term, sourceChunks: Iterable[Chunk] = Set.empty, sourceTerms: Iterable[Term] = Set.empty): Term = decider match {
    case daDecider: DependencyAnalysisDeciderFeatures =>
      if (!daDecider.isDependencyAnalysisEnabled || term.equals(True) || sourceChunks.size + sourceTerms.size == 0)
        return term

      val labelNode = daDecider.getOrCreateAnalysisLabelNode(sourceChunks, sourceTerms)
      labelNode.map(n => Implies(n.term, term)).getOrElse(term)
    case _ => term
  }

  def handleAndGetUpdatedAnalysisInfos(decider: Decider, analysisInfos: DependencyAnalysisInfos, info: Info, node: ast.Node): DependencyAnalysisInfos = decider match {
    case daDecider: DependencyAnalysisDeciderFeatures =>
      val newAnalysisInfos = analysisInfos.addInfo(info, node)
      info.getAllInfos[AdditionalDependencyNodeInfo].foreach {
        case AdditionalAssertionNode() => daDecider.getDependencyAnalyzer.createAssertOrCheckNode(True, newAnalysisInfos, isCheck = false).foreach(n => {
          daDecider.getDependencyAnalyzer.addAssertionNode(n)
          if (daDecider.isPathMarkedInfeasible) daDecider.getDependencyAnalyzer.addDependency(daDecider.pcs.getCurrentInfeasibilityNode, Some(n.id))
        })
        case AdditionalAssumptionNode() => daDecider.getDependencyAnalyzer.addAssumption(True, newAnalysisInfos)
      }
      newAnalysisInfos
    case _ => analysisInfos
  }
  /**
   *
   * @param name Optional name for the result graph.
   * @param dependencyGraphInterpreters The graphs to be joined.
   * @return A dependency graph interpreter operating on a new dependency graph that represents all input graphs and
   *         all dependencies between them.
   * The new graph is built by adding all existing nodes and edges of all input graphs and joining them
   * via the join information stored in each node.
   */
  def joinGraphsAndGetInterpreter(name: String, dependencyGraphInterpreters: Set[DependencyGraphInterpreter[IntraProcedural]]): DependencyGraphInterpreter[Final] = {
    val newGraph = new DependencyGraph[Final]

    newGraph.addAssumptionNodes(dependencyGraphInterpreters.flatMap (_.getGraph.getAssumptionNodes))
    newGraph.addAssertionNodes(dependencyGraphInterpreters.flatMap (_.getGraph.getAssertionNodes))
    dependencyGraphInterpreters foreach (interpreter => interpreter.getGraph.getAllEdges foreach {case (t, deps) => newGraph.addEdges(deps, t)})

    val joinSourceNodes = dependencyGraphInterpreters flatMap(i => i.joinSourceNodes)
    val joinSinkNodes   = dependencyGraphInterpreters flatMap(i => i.joinSinkNodes)

    def getJoinNodesByJoinInfo(candidateNodes: Set[DependencyAnalysisNode], joinType: JoinType) = {
      candidateNodes
        .flatMap(node => node.joinInfos.filter(_.joinType.equals(joinType)).map((_, node)))
        .groupBy(_._1)
        .view.mapValues(_.map(_._2))
        .toMap
    }

    val sourceNodesByJoinInfo = getJoinNodesByJoinInfo(joinSourceNodes, JoinType.Source)
    val sinkNodesByJoinInfo = getJoinNodesByJoinInfo(joinSinkNodes, JoinType.Sink)

    sinkNodesByJoinInfo.foreach{case (joinInfo, sinkNodes) =>
      val matchingSourceNodes = sourceNodesByJoinInfo.filter{case (sourceJoinInfo, _) => sourceJoinInfo.matches(joinInfo)}.values.flatten.toSet
      addEdgesConnectingMethods(newGraph, joinInfo, matchingSourceNodes, sinkNodes)
    }

    val newInterpreter = new DependencyGraphInterpreter[Final](name, newGraph, dependencyGraphInterpreters.toList.flatMap(_.getErrors))
    newInterpreter
  }

  private def addEdgesConnectingMethods(newGraph: DependencyGraph[Final], joinInfo: SimpleDependencyAnalysisJoin, sourceNodes: Set[DependencyAnalysisNode], sinkNodes: Set[DependencyAnalysisNode]): Unit = {
    if (joinInfo.edgeType.equals(EdgeType.Up)) {
      val directDepsOfSources = if(!Verifier.config.disableDependencyAnalysisJoinPrecisionOpt()) {
        // Preconditions are connected to the dependencies required to prove them at all call sites. However, they do not depend on the calls themselves.
        sourceNodes.groupBy(_.sourceInfo).flatMap(t => newGraph.getDirectDependenciesByNode(t._2, includeInfeasibilityNodes = true, includeUpwardEdges = true, includeDownwardEdges = true))
      } else {
        // Connect preconditions directly to call and therefore, indirectly to all its dependencies -> imprecise but might be faster and
        // more user-friendly since it becomes apparent which call introduced these indirect dependencies.
        sourceNodes.map(_.id)
      }
      newGraph.addEdgesConnectingMethodsUpwards(directDepsOfSources, sinkNodes.map(_.id))
    } else {
      newGraph.addEdgesConnectingMethodsDownwards(sourceNodes.map(_.id), sinkNodes.map(_.id))
    }
  }
}

class DefaultDependencyAnalyzer(member: Option[ast.Member]) extends DependencyAnalyzer {
  protected var customMergeDependencies: Set[(Set[DependencyAnalysisMergeInfo], Set[DependencyAnalysisMergeInfo])] = Set.empty

  override def getMember: ast.Member = member.get

  override def getNodes: Iterable[DependencyAnalysisNode] = dependencyGraph.getNodes

  private def getNodeIdsByTerm(terms: Set[Term]): Set[Int] = {
    dependencyGraph.getNodes
      .filter(t => terms.contains(t.getTerm))
      .map(_.id)
  }


  override def addNodes(nodes: Iterable[DependencyAnalysisNode]): Unit = {
    nodes foreach dependencyGraph.addNode
  }

  override def addAssumptionNode(node: GeneralAssumptionNode): Unit = dependencyGraph.addAssumptionNode(node)

  override def addAssertionNode(node: GeneralAssertionNode): Unit = dependencyGraph.addAssertionNode(node)

  override def addAssumption(assumption: Term, analysisInfos: DependencyAnalysisInfos, description: Option[String]): Option[Int] = {
    val node = new SimpleAssumptionNode(assumption, description, analysisInfos.getSourceInfo, analysisInfos.getDependencyType.assumptionType, analysisInfos.getMergeInfo, analysisInfos.getJoinInfo, getMember.name)
    addAssumptionNode(node)
    Some(node.id)
  }

  override def addAxiom(assumption: Term, analysisAxiomInfo: DependencyAnalysisAxiomInfo, description: Option[String]): Option[Int] = {
    val analysisInfos = analysisAxiomInfo.analysisInfos
    val node = new AxiomAssumptionNode(assumption, description, analysisInfos.getSourceInfo, analysisInfos.getDependencyType.assumptionType, analysisInfos.getMergeInfo, analysisInfos.getJoinInfo, analysisAxiomInfo.memberStr)
    addAssumptionNode(node)
    Some(node.id)
  }

  override def registerExhaleChunk[CH <: GeneralChunk](sourceChunks: Set[Chunk], buildChunk: Term => CH, perm: Term, labelNodeOpt: Option[LabelNode], analysisInfos: DependencyAnalysisInfos): CH = {
    val labelNode = labelNodeOpt.get
    val chunk = buildChunk(Ite(labelNode.term, perm, NoPerm))
    val chunkNode = addPermissionExhaleNode(chunk, chunk.perm, analysisInfos, labelNode)
    if (chunkNode.isDefined) addDependency(chunkNode, Some(labelNode.id))
    chunk
  }

  override def registerInhaleChunk[CH <: GeneralChunk](sourceChunks: Set[Chunk], buildChunk: Term => CH, perm: Term, labelNodeOpt: Option[LabelNode], analysisInfos: DependencyAnalysisInfos): CH = {
    val labelNode = labelNodeOpt.get
    val chunk = buildChunk(Ite((labelNode.term, perm, NoPerm)))
    val chunkNode = addPermissionInhaleNode(chunk, chunk.perm, analysisInfos, labelNode)
    if (chunkNode.isDefined) addDependency(chunkNode, Some(labelNode.id))
    chunk
  }

  private def addPermissionInhaleNode(chunk: Chunk, permAmount: Term, analysisInfos: DependencyAnalysisInfos, labelNode: LabelNode): Option[Int] = {
    val node = new PermissionInhaleNode(chunk, permAmount, analysisInfos.getSourceInfo, analysisInfos.getDependencyType.assumptionType, analysisInfos.getMergeInfo, labelNode, analysisInfos.getJoinInfo, getMember.name)
    addAssumptionNode(node)
    Some(node.id)
  }

  private def addPermissionExhaleNode(chunk: Chunk, permAmount: Term, analysisInfos: DependencyAnalysisInfos, labelNode: LabelNode): Option[Int] = {
    val node = new PermissionExhaleNode(chunk, permAmount, analysisInfos.getSourceInfo, analysisInfos.getDependencyType.assertionType, analysisInfos.getMergeInfo, labelNode, analysisInfos.getJoinInfo, getMember.name)
    addAssertionNode(node)
    Some(node.id)
  }

  override def createLabelNode(label: Var, sourceChunks: Iterable[Chunk], sourceTerms: Iterable[Term]): Option[LabelNode] = {
    val labelNode = new LabelNode(label, getMember.name)
    addAssumptionNode(labelNode)
    dependencyGraph.addEdges(getNodeIdsByTerm(sourceTerms.toSet), labelNode.id)
    Some(labelNode)
  }

  override def createAssertOrCheckNode(term: Term, analysisInfos: DependencyAnalysisInfos, isCheck: Boolean): Option[GeneralAssertionNode] = {
    if (isCheck)
      Some(new SimpleCheckNode(term, analysisInfos.getSourceInfo, analysisInfos.getDependencyType.assertionType, analysisInfos.getMergeInfo, analysisInfos.getJoinInfo, getMember.name))
    else
      Some(new SimpleAssertionNode(term, analysisInfos.getSourceInfo, analysisInfos.getDependencyType.assertionType, analysisInfos.getMergeInfo, analysisInfos.getJoinInfo, getMember.name))
  }
  
  private def addAssertNode(term: Term, analysisInfos: DependencyAnalysisInfos): Option[Int] = {
    val node = createAssertOrCheckNode(term, analysisInfos, isCheck=false)
    node foreach addAssertionNode
    node map (_.id)
  }

  override def addAssertFalseNode(isCheck: Boolean, analysisInfos: DependencyAnalysisInfos): Option[Int] = {
    val node = createAssertOrCheckNode(False, analysisInfos, isCheck)
    addAssertionNode(node.get)
    node.map(_.id)
  }

  override def addInfeasibilityNode(isCheck: Boolean, analysisInfos: DependencyAnalysisInfos): Option[Int] = {
    val node = new InfeasibilityNode(analysisInfos.getSourceInfo, analysisInfos.getDependencyType.assumptionType, getMember.name)
    addAssumptionNode(node)
    Some(node.id)
  }

  override def addAssertionFailedNode(failedAssertion: Term, analysisInfos: DependencyAnalysisInfos): Option[Int] = {
    val assumeNode = new SimpleAssumptionNode(failedAssertion, None, analysisInfos.getSourceInfo, analysisInfos.getDependencyType.assertionType, analysisInfos.getMergeInfo, analysisInfos.getJoinInfo, getMember.name)
    val assertFailedNode = new SimpleAssertionNode(failedAssertion, analysisInfos.getSourceInfo, analysisInfos.getDependencyType.assertionType, analysisInfos.getMergeInfo, analysisInfos.getJoinInfo, getMember.name, hasFailed=true)
    dependencyGraph.addNode(assumeNode)
    dependencyGraph.addNode(assertFailedNode)
    dependencyGraph.addEdges(Set(assumeNode.id), assertFailedNode.id)
    Some(assertFailedNode.id)
  }


  override def addDependency(source: Option[Int], dest: Option[Int]): Unit = {
    if (source.isDefined && dest.isDefined)
      dependencyGraph.addEdges(source.get, Set(dest.get))
  }

  override def processUnsatCoreAndAddDependencies(dep: String, assertionLabel: String): Unit = {
    val assumptionLabels = dep.replace("(", "").replace(")", "").split(" ")
    val assertionId = DependencyAnalyzer.getIdFromLabel(assertionLabel)
    val assumptionIds = assumptionLabels.map(DependencyAnalyzer.getIdFromLabel).toSet
    if (!assumptionIds.contains(assertionId))
      dependencyGraph.addVacuousProof(assertionId)
    dependencyGraph.addEdges(assumptionIds.diff(Set(assertionId)), assertionId)
  }

  override def addDependenciesForAbstractMembers(sourceExps: Seq[ast.Exp], targetExps: Seq[ast.Exp], analysisInfos: DependencyAnalysisInfos): Unit = {
    val sourceNodeIds = sourceExps.flatMap(e => addAssumption(True, analysisInfos.addInfo(e.info, e).withJoinInfo(EvalStackDependencyAnalysisJoin(JoinType.Sink, EdgeType.Up))))
    val targetNodes = targetExps.flatMap(e => addAssertNode(True, analysisInfos.addInfo(e.info, e).withJoinInfo(EvalStackDependencyAnalysisJoin(JoinType.Source, EdgeType.Down))))
    dependencyGraph.addEdges(sourceNodeIds, targetNodes)
  }

  override def addCustomDependenciesBetweenMergeInfos(sourceExps: Seq[Exp], targetExps: Seq[Exp]): Unit = {
    val sourceMergeInfos = sourceExps.flatMap(_.info.getUniqueInfo[DependencyAnalysisMergeInfo]).filter(_.isMerge).toSet
    val targetMergeInfos = targetExps.flatMap(_.info.getUniqueInfo[DependencyAnalysisMergeInfo]).filter(_.isMerge).toSet

    customMergeDependencies = Set((sourceMergeInfos, targetMergeInfos)) ++ customMergeDependencies
  }

  protected def addCustomMergeDependencies(mergedGraph: DependencyGraph[IntraProcedural]): Unit = {
    customMergeDependencies.foreach{ case (sourceMergeInfos, targetMergeInfos) =>
      val sourceNodes = mergedGraph.getNodes.filter(node => sourceMergeInfos.contains(node.mergeInfo)).map(_.id)
      val targetNodes = mergedGraph.getNodes.filter(node => targetMergeInfos.contains(node.mergeInfo)).map(_.id)
      mergedGraph.addEdges(sourceNodes, targetNodes)
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
    val mergedGraph = if (Verifier.config.enableDependencyAnalysisDebugging()) dependencyGraph.asInstanceOf[DependencyGraph[IntraProcedural]] else buildAndGetMergedGraph()
    addTransitiveEdges(mergedGraph)
    if (!Verifier.config.enableDependencyAnalysisDebugging()) mergedGraph.removeInternalNodes()
    Some(mergedGraph)
  }

  /**
   * Adds edges between the nodes with identical merge info and the ones to be connected as given by the custom merge dependencies
   * to the merged graph. This step is necessary to ensure that the low-level graph is connected and encodes all direct
   * and indirect dependencies.
   */
  private def addTransitiveEdges(mergedGraph: DependencyGraph[IntraProcedural]): Unit = {
    val nodesPerSourceInfo = mergedGraph.getNodes.filter(_.mergeInfo.isMerge).groupBy(_.mergeInfo)
    nodesPerSourceInfo foreach {case (_, nodes) =>
      val asserts = nodes.filter(_.isInstanceOf[GeneralAssertionNode])
      val assumes = nodes.filter(n => n.isInstanceOf[GeneralAssumptionNode] && !n.isInstanceOf[LabelNode])
      mergedGraph.addEdges(asserts.map(_.id), assumes.map(_.id))
      val checks = asserts.filter(_.isInstanceOf[SimpleCheckNode])
      val notChecks = nodes.filter(n => !n.isInstanceOf[SimpleCheckNode])
      mergedGraph.addEdges(checks.map(_.id), notChecks.map(_.id)) // TODO ake: why do we need this?
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
    def keepNode(n: DependencyAnalysisNode): Boolean = !n.mergeInfo.isMerge || n.joinInfos.nonEmpty || n.isInstanceOf[InfeasibilityNode] || n.isInstanceOf[AxiomAssumptionNode]

    val mergedGraph = new DependencyGraph[IntraProcedural]
    val nodeMap = mutable.HashMap[Int, Int]()

    dependencyGraph.getAssumptionNodes.filter(keepNode).foreach { n =>
      nodeMap.put(n.id, n.id)
      mergedGraph.addAssumptionNode(n)
    }
    val assumptionNodesBySource = dependencyGraph.getAssumptionNodes.filter(!keepNode(_)).groupBy(n => (n.sourceInfo, n.assumptionType, n.mergeInfo, n.joinInfos, n.memberStr))
    assumptionNodesBySource foreach { case ((sourceInfo, assumptionType, mergeInfo, joinInfos, memberStr), assumptionNodes) =>
      if (assumptionNodes.nonEmpty) {
        val newNode = new SimpleAssumptionNode(True, None, sourceInfo, assumptionType, mergeInfo, joinInfos, memberStr)
        assumptionNodes foreach (n => nodeMap.put(n.id, newNode.id))
        mergedGraph.addAssumptionNode(newNode)
      }
    }

    dependencyGraph.getAssertionNodes.filter(keepNode).foreach { n =>
      nodeMap.put(n.id, n.id)
      mergedGraph.addAssertionNode(n)
    }
    val assertionNodesBySource = dependencyGraph.getAssertionNodes.filter(!keepNode(_)).groupBy(n => (n.sourceInfo, n.assumptionType, n.mergeInfo, n.joinInfos, n.memberStr))
    assertionNodesBySource foreach { case ((sourceInfo, assumptionType, mergeInfo, joinInfos, memberStr), assertionNodes) =>
      if (assertionNodes.nonEmpty) {
        val newNode = new SimpleAssertionNode(True, sourceInfo, assumptionType, mergeInfo, joinInfos, memberStr, hasFailed=assertionNodes.exists(_.hasFailed))
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
  override def addAssertionWithDepToInfeasNode(infeasNodeId: Option[Int], analysisInfos: DependencyAnalysisInfos): Unit = {
    val newAssertionNodeId = addAssertNode(False, analysisInfos)
    addDependency(infeasNodeId, newAssertionNodeId)
  }

}

/**
 * This DependencyAnalyzer implementation is used by default and does nothing.
 */
class NoDependencyAnalyzer extends DependencyAnalyzer {

  override def getMember: ast.Member = ast.Method("none", Seq.empty, Seq.empty, Seq.empty, Seq.empty, None)()

  override def getNodes: Iterable[DependencyAnalysisNode] = Set.empty

  override def addNodes(nodes: Iterable[DependencyAnalysisNode]): Unit = {}
  override def addAssertionNode(node: GeneralAssertionNode): Unit = {}
  override def addAssumptionNode(node: GeneralAssumptionNode): Unit = {}
  override def addAssumption(assumption: Term, analysisInfos: DependencyAnalysisInfos, description: Option[String] = None): Option[Int] = None
  override def addAxiom(assumption: Term, analysisAxiomInfo: DependencyAnalysisAxiomInfo, description: Option[String]): Option[Int] = None
  override def createLabelNode(labelTerm: Var, sourceChunks: Iterable[Chunk], sourceTerms: Iterable[Term]): Option[LabelNode] = None

  override def createAssertOrCheckNode(term: Term, analysisInfos: DependencyAnalysisInfos, isCheck: Boolean): Option[GeneralAssertionNode] = None
  override def addAssertFalseNode(isCheck: Boolean, analysisInfos: DependencyAnalysisInfos): Option[Int] = None
  override def addInfeasibilityNode(isCheck: Boolean, analysisInfos: DependencyAnalysisInfos): Option[Int] = None
  override def addAssertionFailedNode(failedAssertion: Term, analysisInfos: DependencyAnalysisInfos): Option[Int] = None

  override def addDependency(source: Option[Int], dest: Option[Int]): Unit = {}
  override def processUnsatCoreAndAddDependencies(dep: String, assertionLabel: String): Unit = {}
  override def addDependenciesForAbstractMembers(sourceExps: Seq[ast.Exp], targetExps: Seq[ast.Exp], analysisInfos: DependencyAnalysisInfos): Unit = {}

  override def buildFinalGraph(): Option[DependencyGraph[IntraProcedural]] = None

  override def addCustomDependenciesBetweenMergeInfos(sourceExps: Seq[Exp], targetExps: Seq[Exp]): Unit = {}

}
