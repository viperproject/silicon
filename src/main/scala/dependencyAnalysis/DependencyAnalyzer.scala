package viper.silicon.dependencyAnalysis

import viper.silicon.dependencyAnalysis.AssumptionType.AssumptionType
import viper.silicon.dependencyAnalysis.DependencyAnalyzer.{runtimeOverheadPermissionNodes, startTimeMeasurement, stopTimeMeasurementAndAddToTotal, timeToProcessUnsatCore}
import viper.silicon.interfaces.state.{Chunk, GeneralChunk}
import viper.silicon.state.terms._
import viper.silicon.verifier.Verifier
import viper.silver.ast

import java.util.concurrent.atomic.AtomicLong
import scala.collection.mutable


trait DependencyAnalyzer {
  protected val dependencyGraph: DependencyGraph = new DependencyGraph()
  protected var isClosed_ = false

  def disableTransitiveEdges(): Unit = {
    isClosed_ = true
  }

  def enableTransitiveEdges(): Unit = {
    isClosed_ = false
  }

  def getMember: Option[ast.Member]

  def getNodes: Iterable[DependencyAnalysisNode]
  def getChunkInhaleNode(chunk: Chunk): Option[PermissionInhaleNode]

  def addNodes(nodes: Iterable[DependencyAnalysisNode]): Unit
  def addNode(node: DependencyAnalysisNode): Unit
  def addAssumption(assumption: Term, analysisSourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType, description: Option[String] = None): Option[Int]
  def addAxiom(assumption: Term, analysisSourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType, description: Option[String] = None): Option[Int]
  def registerInhaleChunk[CH <: GeneralChunk](sourceChunks: Set[Chunk], buildChunk: Term => CH, perm: Term, labelNode: Option[LabelNode], analysisInfo: AnalysisInfo, isExhale: Boolean): CH = buildChunk(perm)
  def registerExhaleChunk[CH <: GeneralChunk](sourceChunks: Set[Chunk], buildChunk: Term => CH, perm: Term, analysisInfo: AnalysisInfo): CH = buildChunk(perm)
  def createLabelNode(label: Var, sourceChunks: Iterable[Chunk], sourceTerms: Iterable[Term]): Option[LabelNode]

  def createAssertOrCheckNode(term: Term, assumptionType: AssumptionType, analysisSourceInfo: AnalysisSourceInfo, isCheck: Boolean): Option[GeneralAssertionNode]
  def addAssertFalseNode(isCheck: Boolean, assumptionType: AssumptionType, sourceInfo: AnalysisSourceInfo): Option[Int]
  def addInfeasibilityNode(isCheck: Boolean, sourceInfo: AnalysisSourceInfo): Option[Int]

  def addDependency(source: Option[Int], dest: Option[Int]): Unit
  def processUnsatCoreAndAddDependencies(dep: String, assertionLabel: String): Unit
  def addPermissionDependencies(sourceChunks: Set[Chunk], sourceTerms: Set[Term], targetChunk: Chunk): Unit
  def addCustomTransitiveDependency(sourceSourceInfo: AnalysisSourceInfo, targetSourceInfo: AnalysisSourceInfo): Unit

  /**
   * Adds dependencies between all pairs of sourceExps and targetExps, where sourceExps should be preconditions and
   * targetExps should be postconditions of an abstract function or method.
   */
  def addDependenciesForExplicitPostconditions(sourceExps: Seq[ast.Exp], targetExps: Seq[ast.Exp]): Unit

  /**
   * Adds edges connecting nodes representing function postconditions with the corresponding axiom nodes.
   */
  def addFunctionAxiomEdges(): Unit

  /**
   * Adds an assertion and assumption node with the given analysis source info and dependencies to the current infeasibility node.
   */
  def addInfeasibilityDepToStmt(infeasNodeId: Option[Int], analysisSourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Unit = {}

  /**
   * @return the final dependency graph representing all direct and transitive dependencies
   */
  def buildFinalGraph(): Option[DependencyGraph]
}

object DependencyAnalyzer {
  val analysisLabelName: String = "$$analysisLabel$$"
  private val assumptionTypeAnnotationKey = "assumptionType"
  private val enableDependencyAnalysisAnnotationKey = "enableDependencyAnalysis"
  val timeToVerifyAndCollectDependencies: AtomicLong = new AtomicLong(0)
  val timeToVerifyAndBuildFinalGraph: AtomicLong = new AtomicLong(0)
  val timeOfPostprocessing: AtomicLong = new AtomicLong(0)
  val timeToAddNodes: AtomicLong = new AtomicLong(0)
  val timeToAddEdges: AtomicLong = new AtomicLong(0)
  val timeToExtractCandidateNodes: AtomicLong = new AtomicLong(0)
  val timeForFunctionJoin: AtomicLong = new AtomicLong(0)
  val timeForMethodJoin: AtomicLong = new AtomicLong(0)
  val runtimeOverheadPermissionNodes: AtomicLong = new AtomicLong(0)
  val timeToExtractUnsatCore: AtomicLong = new AtomicLong(0)
  val timeToProcessUnsatCore: AtomicLong = new AtomicLong(0)

  def startTimeMeasurement(): Long = {
    if(!Verifier.config.enableDependencyAnalysisProfiling()) return 0
    System.nanoTime()
  }

  def stopTimeMeasurementAndAddToTotal(startTime: Long, total: AtomicLong): Unit = {
    if(!Verifier.config.enableDependencyAnalysisProfiling()) return

    val endTime = System.nanoTime()
    total.addAndGet(endTime - startTime)
  }

  // TODO ake: remove all profiling artifacts
  def printProfilingResults(): Unit = {
    if(!Verifier.config.enableDependencyAnalysisProfiling()) return
    println(s"Overall runtime = time spent on verification and building the final graph: ${timeToVerifyAndBuildFinalGraph.get() / 1e6}ms")
    println(s"This runtime can be categorized into the following, fine-grained measurements.")
    println(s"  Time spent on verification and collecting low-level dependencies: ${timeToVerifyAndCollectDependencies.get() / 1e6}ms")
    println(s"    Time spent on adding explicit permission nodes: ${runtimeOverheadPermissionNodes.get() / 1e6}ms")
    println(s"    Time spent on extracting the unsat core: ${timeToExtractUnsatCore.get() / 1e6}ms")
    println(s"    Time spent on processing the unsat core: ${timeToProcessUnsatCore.get() / 1e6}ms")
    println(s"  Postprocessing: ${timeOfPostprocessing.get() / 1e6}ms")
    println(s"    Time spent on adding nodes: ${timeToAddNodes.get() / 1e6}ms")
    println(s"    Time spent on adding edges: ${timeToAddEdges.get() / 1e6}ms")
    println(s"    Time spent on extracting candidate nodes: ${timeToExtractCandidateNodes.get() / 1e6}ms")
    println(s"    Time spent for joins over function calls: ${timeForFunctionJoin.get() / 1e6}ms")
    println(s"    Time spent for joins over method calls: ${timeForMethodJoin.get() / 1e6}ms")
  }

  private def extractAnnotationFromInfo(info: ast.Info, annotationKey: String): Option[Seq[String]] = {
    info.getAllInfos[ast.AnnotationInfo]
      .filter(_.values.contains(annotationKey))
      .map(_.values(annotationKey)).headOption
  }

  def extractAssumptionTypeFromInfo(info: ast.Info): Option[AssumptionType] = {
    val annotation = extractAnnotationFromInfo(info, assumptionTypeAnnotationKey)
    if(annotation.isDefined && annotation.get.nonEmpty) AssumptionType.fromString(annotation.get.head)
    else None
  }

  def extractDependencyTypeFromInfo(info: ast.Info): Option[DependencyType] = {
    val annotation = extractAnnotationFromInfo(info, assumptionTypeAnnotationKey)
    val dependencyAnalysisInfo = info.getUniqueInfo[FrontendDependencyAnalysisInfo]
    if(annotation.isDefined && annotation.get.nonEmpty) AssumptionType.fromString(annotation.get.head).map(DependencyType.make)
    else if(dependencyAnalysisInfo.isDefined) dependencyAnalysisInfo.get.dependencyType
    else None
  }

  def extractEnableAnalysisFromInfo(info: ast.Info): Option[Boolean] = {
    val annotation = extractAnnotationFromInfo(info, enableDependencyAnalysisAnnotationKey)
    if(annotation.isDefined && annotation.get.nonEmpty) annotation.get.head.toBooleanOption else None
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

  def isAssertionLabel(label: String): Boolean = label.startsWith("assertion_")

  def isAssumptionLabel(label: String): Boolean = label.startsWith("assumption_")

  def isAxiomLabel(label: String): Boolean = label.startsWith("axiom_")

  /**
   *
   * @param name Optional name for the result graph.
   * @param dependencyGraphInterpreters The graphs which should be joined.
   * @return A dependency graph interpreter operating on a new dependency graph that represents all input graphs and
   *         dependencies between them.
   * The new graph is built by adding all existing nodes and edges of all input graphs and joining them via postconditions
   * of functions and methods.
   */
  def joinGraphsAndGetInterpreter(name: String, dependencyGraphInterpreters: Iterable[DependencyGraphInterpreter]): DependencyGraphInterpreter = {
    var startTime = startTimeMeasurement()
    val newGraph = new DependencyGraph

    newGraph.addNodes(dependencyGraphInterpreters.flatMap (_.getGraph.getNodes))
    stopTimeMeasurementAndAddToTotal(startTime, timeToAddNodes)
    startTime = startTimeMeasurement()
    dependencyGraphInterpreters foreach (interpreter => interpreter.getGraph.getAllEdges foreach {case (t, deps) => newGraph.addEdges(deps, t)})
    stopTimeMeasurementAndAddToTotal(startTime, timeToAddEdges)
    startTime = startTimeMeasurement()
    val joinCandidateNodes = dependencyGraphInterpreters flatMap(_.getJoinCandidateNodes)
    stopTimeMeasurementAndAddToTotal(startTime, timeToExtractCandidateNodes)

    startTime = startTimeMeasurement()
    // axioms assumed by every method / function should depend on the assertions that justify them
    // hence, we add edges from function postconditions & bodies to the corresponding axioms
    val axiomAssertionNodes = joinCandidateNodes
      .filter(n => (n.isInstanceOf[GeneralAssertionNode] && AssumptionType.postconditionTypes.contains(n.assumptionType))
      || AssumptionType.FunctionBody.equals(n.assumptionType))
      .groupBy(_.sourceInfo.getTopLevelSource)
      .view.mapValues(_.map(_.id))
      .toMap
    joinCandidateNodes.filter(_.isInstanceOf[AxiomAssumptionNode])
      .groupBy(n => n.sourceInfo)
      .map{case (sourceInfo, axiomNodes) => (axiomNodes.map(_.id), axiomAssertionNodes.getOrElse(sourceInfo.getTopLevelSource, Seq.empty))}
      .foreach{case (axiomNodeIds, assertionNodeIds) =>
        newGraph.addEdges(assertionNodeIds, axiomNodeIds) // TODO ake: maybe we could merge the axiom nodes here since they represent the same axiom?
    }

    stopTimeMeasurementAndAddToTotal(startTime, timeForFunctionJoin)
    startTime = startTimeMeasurement()

    // postconditions of methods assumed by every method call should depend on the assertions that justify them
    // hence, we add edges from assertions of method postconditions to assumptions of the same postcondition (at method calls)
    val relevantAssumptionNodes = joinCandidateNodes
      .filter(node => node.isInstanceOf[GeneralAssumptionNode] && AssumptionType.postconditionTypes.contains(node.assumptionType))
      .groupBy(_.sourceInfo.getFineGrainedSource)
      .view.mapValues(_.map(_.id))
      .toMap
    joinCandidateNodes.filter(node => node.isInstanceOf[GeneralAssertionNode] && AssumptionType.postconditionTypes.contains(node.assumptionType))
      .map(node => (node.id, relevantAssumptionNodes.getOrElse(node.sourceInfo.getTopLevelSource, Seq.empty)))
      .foreach { case (src, targets) => newGraph.addEdges(src, targets)}

    stopTimeMeasurementAndAddToTotal(startTime, timeForMethodJoin)

    val newInterpreter = new DependencyGraphInterpreter(name, newGraph, dependencyGraphInterpreters.toList.flatMap(_.getErrors))
    newInterpreter
  }
}

class DefaultDependencyAnalyzer(member: ast.Member) extends DependencyAnalyzer {
  protected var proofCoverage: Double = 0.0

  override def getMember: Option[ast.Member] = Some(member)

  override def getNodes: Iterable[DependencyAnalysisNode] = dependencyGraph.nodes

  override def getChunkInhaleNode(chunk: Chunk): Option[PermissionInhaleNode] = {
    val inhaleNode = dependencyGraph.nodes
      .filter(c => c.isInstanceOf[PermissionInhaleNode] && chunk.equals(c.asInstanceOf[ChunkAnalysisInfo].getChunk))
      .map(_.asInstanceOf[PermissionInhaleNode])
    assert(inhaleNode.size == 1)
    inhaleNode.headOption
  }

  private def getChunkNodeIds(oldChunks: Set[Chunk]): Set[Int] = {
    dependencyGraph.nodes
      .filter(c => c.isInstanceOf[PermissionInhaleNode] && oldChunks.contains(c.asInstanceOf[ChunkAnalysisInfo].getChunk))
      .map(_.id).toSet
  }

  private def getNodeIdsByTerm(terms: Set[Term]): Set[Int] = {
    dependencyGraph.nodes
      .filter(t => terms.contains(t.getTerm))
      .map(_.id).toSet
  }


  override def addNodes(nodes: Iterable[DependencyAnalysisNode]): Unit = {
    dependencyGraph.addNodes(nodes)
  }

  override def addNode(node: DependencyAnalysisNode): Unit = {
    dependencyGraph.addNode(node)
  }

  // adding assumption nodes
  override def addAssumption(assumption: Term, analysisSourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType, description: Option[String]): Option[Int] = {
    val node = SimpleAssumptionNode(assumption, description, analysisSourceInfo, assumptionType, isClosed_)
    addNode(node)
    Some(node.id)
  }

  override def addAxiom(assumption: Term, analysisSourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType, description: Option[String]): Option[Int] = {
    val node = AxiomAssumptionNode(assumption, description, analysisSourceInfo, assumptionType, isClosed_)
    addNode(node)
    Some(node.id)
  }

  override def registerExhaleChunk[CH <: GeneralChunk](sourceChunks: Set[Chunk], buildChunk: Term => CH, perm: Term, analysisInfo: AnalysisInfo): CH = {
    val startTime = startTimeMeasurement()
    val chunk = buildChunk(perm)
    val chunkNode = addPermissionExhaleNode(chunk, chunk.perm, analysisInfo.sourceInfo, analysisInfo.assumptionType)
    addPermissionDependencies(sourceChunks, Set(), chunkNode)
    stopTimeMeasurementAndAddToTotal(startTime, runtimeOverheadPermissionNodes)
    chunk
  }

  override def registerInhaleChunk[CH <: GeneralChunk](sourceChunks: Set[Chunk], buildChunk: Term => CH, perm: Term, labelNodeOpt: Option[LabelNode], analysisInfo: AnalysisInfo, isExhale: Boolean): CH = {
    val startTime = startTimeMeasurement()
    val labelNode = labelNodeOpt.get
    val chunk = buildChunk(Ite(labelNode.term, perm, NoPerm))
    val chunkNode = addPermissionInhaleNode(chunk, chunk.perm, analysisInfo.sourceInfo, analysisInfo.assumptionType, labelNode)
    if(chunkNode.isDefined)
      addDependency(chunkNode, Some(labelNode.id))
    addPermissionDependencies(sourceChunks, Set(), chunkNode)
    stopTimeMeasurementAndAddToTotal(startTime, runtimeOverheadPermissionNodes)
    chunk
  }

  private def addPermissionInhaleNode(chunk: Chunk, permAmount: Term, sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType, labelNode: LabelNode): Option[Int] = {
    val node = PermissionInhaleNode(chunk, permAmount, sourceInfo, assumptionType, isClosed_, labelNode)
    addNode(node)
    Some(node.id)
  }

  private def addPermissionExhaleNode(chunk: Chunk, permAmount: Term, sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Option[Int] = {
    val node = PermissionExhaleNode(chunk, permAmount, sourceInfo, assumptionType, isClosed_)
    addNode(node)
    addPermissionDependencies(Set(chunk), Set(), Some(node.id))
    Some(node.id)
  }

  override def createLabelNode(label: Var, sourceChunks: Iterable[Chunk], sourceTerms: Iterable[Term]): Option[LabelNode] = {
    val labelNode = LabelNode(label)
    addNode(labelNode)
    dependencyGraph.addEdges(getChunkNodeIds(sourceChunks.toSet) ++ getNodeIdsByTerm(sourceTerms.toSet), labelNode.id)
    Some(labelNode)
  }

  // adding assertion nodes
  override def createAssertOrCheckNode(term: Term, assumptionType: AssumptionType, analysisSourceInfo: AnalysisSourceInfo, isCheck: Boolean): Option[GeneralAssertionNode] = {
    if(isCheck)
      Some(SimpleCheckNode(term, assumptionType, analysisSourceInfo, isClosed_))
    else
      Some(SimpleAssertionNode(term, assumptionType, analysisSourceInfo, isClosed_))
  }
  
  def addAssertNode(term: Term, assumptionType: AssumptionType, analysisSourceInfo: AnalysisSourceInfo): Option[Int] = {
    val node = createAssertOrCheckNode(term, assumptionType, analysisSourceInfo, isCheck=false)
    node foreach addNode
    node map (_.id)
  }

  override def addAssertFalseNode(isCheck: Boolean, assumptionType: AssumptionType, sourceInfo: AnalysisSourceInfo): Option[Int] = {
    val node = createAssertOrCheckNode(False, assumptionType, sourceInfo, isCheck)
    addNode(node.get)
    node.map(_.id)
  }

  override def addInfeasibilityNode(isCheck: Boolean, sourceInfo: AnalysisSourceInfo): Option[Int] = {
    val node = InfeasibilityNode(sourceInfo)
    addNode(node)
    Some(node.id)
  }


  // adding dependencies
  override def addDependency(source: Option[Int], dest: Option[Int]): Unit = {
    if(source.isDefined && dest.isDefined)
      dependencyGraph.addEdges(source.get, Set(dest.get))
  }

  override def processUnsatCoreAndAddDependencies(dep: String, assertionLabel: String): Unit = {
    val startTime = startTimeMeasurement()
    val assumptionLabels = dep.replace("(", "").replace(")", "").split(" ")
    val assumptionIds = assumptionLabels.filter(DependencyAnalyzer.isAssumptionLabel).map(DependencyAnalyzer.getIdFromLabel)
    val assertionIdsFromUnsatCore = assumptionLabels.filter(DependencyAnalyzer.isAssertionLabel).map(DependencyAnalyzer.getIdFromLabel)
    val assertionIdFromLabel = DependencyAnalyzer.getIdFromLabel(assertionLabel)
    val assertionIds = assertionIdFromLabel +: assertionIdsFromUnsatCore
    dependencyGraph.addEdges(assumptionIds, assertionIds)
    val axiomIds = assumptionLabels.filter(DependencyAnalyzer.isAxiomLabel).map(DependencyAnalyzer.getIdFromLabel)
    dependencyGraph.addEdges(axiomIds, assertionIds)
    stopTimeMeasurementAndAddToTotal(startTime, timeToProcessUnsatCore)
  }

  private def addPermissionDependencies(sourceChunks: Set[Chunk], sourceTerms: Set[Term], newChunkNodeId: Option[Int]): Unit = {
    if(newChunkNodeId.isEmpty) return

    val sourceNodeIds = getChunkNodeIds(sourceChunks).filter(id => id != newChunkNodeId.get) ++ getNodeIdsByTerm(sourceTerms)
    dependencyGraph.addEdges(sourceNodeIds, newChunkNodeId.get)
  }

  override def addPermissionDependencies(sourceChunks: Set[Chunk], sourceTerms: Set[Term], newChunk: Chunk): Unit = {
    val startTime = startTimeMeasurement()
    val newChunkId = dependencyGraph.nodes
      .filter(c => c.isInstanceOf[PermissionInhaleNode] && c.isInstanceOf[ChunkAnalysisInfo] && newChunk.equals(c.asInstanceOf[ChunkAnalysisInfo].getChunk))
      .map(_.id).toSet
    addPermissionDependencies(sourceChunks, sourceTerms, newChunkId.headOption)
    stopTimeMeasurementAndAddToTotal(startTime, runtimeOverheadPermissionNodes)
  }

  override def addCustomTransitiveDependency(sourceSourceInfo: AnalysisSourceInfo, targetSourceInfo: AnalysisSourceInfo): Unit = {
    // TODO ake: remove this since this is already done in buildFinalGraph()?
//    val sourceNodes = assumptionGraph.nodes filter (n => n.isInstanceOf[GeneralAssertionNode] && n.sourceInfo.getSourceForTransitiveEdges.equals(sourceSourceInfo.getSourceForTransitiveEdges))
//    val targetNodes = assumptionGraph.nodes filter (n => n.isInstanceOf[GeneralAssumptionNode] && n.sourceInfo.getSourceForTransitiveEdges.equals(targetSourceInfo.getSourceForTransitiveEdges))
//    assumptionGraph.addEdges(sourceNodes map (_.id), targetNodes map (_.id))
  }

  override def addDependenciesForExplicitPostconditions(sourceExps: Seq[ast.Exp], targetExps: Seq[ast.Exp]): Unit = {
    val sourceNodeIds = sourceExps.flatMap(e => addAssumption(True, AnalysisSourceInfo.createAnalysisSourceInfo(e), AssumptionType.Precondition, None))
    val targetNodes = targetExps.flatMap(e => addAssertNode(True, AssumptionType.ExplicitPostcondition, AnalysisSourceInfo.createAnalysisSourceInfo(e)))
    dependencyGraph.addEdges(sourceNodeIds, targetNodes)
  }

  /**
   *
   * @return the final dependency graph
   * This operation ensures sound computation of transitive dependencies by adding edges between nodes originating from the same
   * source code statement.
   * Further, this operation removes unnecessary details from the graph by, for example, removing label nodes and merging identical nodes.
   */
  override def buildFinalGraph(): Option[DependencyGraph] = {
    dependencyGraph.removeLabelNodes()
    val mergedGraph = if(Verifier.config.enableDependencyAnalysisDebugging()) dependencyGraph else  buildAndGetMergedGraph()
    mergedGraph.addTransitiveEdges()
    Some(mergedGraph)
  }

  override def addFunctionAxiomEdges(): Unit = {
    val axiomNodes = getNodes.filter(_.isInstanceOf[AxiomAssumptionNode])
    val postcondNodes = getNodes.filter(n => AssumptionType.postconditionTypes.contains(n.assumptionType))
    axiomNodes foreach {aNode =>
      val pNodes = postcondNodes filter (_.sourceInfo.toString.equals(aNode.sourceInfo.toString)) map (_.id)
      dependencyGraph.addEdges(pNodes, aNode.id)
    }
  }

  /**
   * Creates a new graph where nodes that only differ in irrelevant information are merged into one node.
   * As a result, this operation removes some lower-level details from the graph.
   * This step can be skipped for debugging purposes by setting the enableDependencyAnalysisDebugging flag. Doing so
   * has no effect on the dependency results but allows to inspect low-level details while debugging and exporting
   * the low-level graph containing all details.
   */
  private def buildAndGetMergedGraph(): DependencyGraph = {
    def keepNode(n: DependencyAnalysisNode): Boolean = n.isClosed || n.isInstanceOf[InfeasibilityNode] || n.isInstanceOf[AxiomAssumptionNode]

    val mergedGraph = new DependencyGraph
    val nodeMap = mutable.HashMap[Int, Int]()
    dependencyGraph.getNodes.filter(keepNode).foreach { n =>
      nodeMap.put(n.id, n.id)
      mergedGraph.addNode(n)
    }

    val nodesBySource = dependencyGraph.getNodes.filter(!keepNode(_)).groupBy(n => (n.sourceInfo, n.assumptionType))

    nodesBySource foreach { case ((sourceInfo, assumptionType), nodes) =>
      val assumptionNodes = nodes.filter(_.isInstanceOf[GeneralAssumptionNode])
      if (assumptionNodes.nonEmpty) {
        val newNode = SimpleAssumptionNode(True, None, sourceInfo, assumptionType, isClosed = false)
        assumptionNodes foreach (n => nodeMap.put(n.id, newNode.id))
        mergedGraph.addNode(newNode)
      }
    }

    nodesBySource foreach { case ((sourceInfo, assumptionType), nodes) =>
      val assertionNodes = nodes.filter(_.isInstanceOf[GeneralAssertionNode]).map(_.asInstanceOf[GeneralAssertionNode])
      if (assertionNodes.nonEmpty) {
        val newNode = SimpleAssertionNode(True, assumptionType, sourceInfo, isClosed = false, hasFailed=assertionNodes.exists(_.hasFailed))
        assertionNodes foreach (n => nodeMap.put(n.id, newNode.id))
        mergedGraph.addNode(newNode)
      }
    }

    dependencyGraph.getAllEdges foreach { case (target, deps) =>
      val newTarget = nodeMap.getOrElse(target, target)
      mergedGraph.addEdges(deps.map(d => nodeMap.getOrElse(d, d)), newTarget)
    }

    mergedGraph
  }

  /**
   * Adds an assertion and assumption node with the given analysis source info and dependencies to the current infeasibility node.
   * If the infeasibility node is not defined, this operation does nothing.
   * The resulting assertion node is required to detect dependencies of the source statement/expression on infeasible paths.
   * The resulting assumption node is required to ensure that unreachable statements/expressions are represented in the graph and
   * thus taken into account by graph queries, e.g. when determining uncovered statements or computing coverage.
   */
  override def addInfeasibilityDepToStmt(infeasNodeId: Option[Int], analysisSourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Unit = {
    val newAssertionNodeId = addAssertNode(False, assumptionType, analysisSourceInfo)
    addDependency(infeasNodeId, newAssertionNodeId)
    val newAssumptionNodeId = addAssumption(False, analysisSourceInfo, assumptionType)
    addDependency(infeasNodeId, newAssumptionNodeId)
  }
}

/**
 * This DependencyAnalyzer implementation is used by default and does nothing.
 */
class NoDependencyAnalyzer extends DependencyAnalyzer {

  override def getMember: Option[ast.Member] = None

  override def getNodes: Iterable[DependencyAnalysisNode] = Set.empty
  override def getChunkInhaleNode(chunk: Chunk): Option[PermissionInhaleNode] = None

  override def addNodes(nodes: Iterable[DependencyAnalysisNode]): Unit = {}
  override def addNode(node: DependencyAnalysisNode): Unit = {}
  override def addAssumption(assumption: Term, analysisSourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType, description: Option[String] = None): Option[Int] = None
  override def addAxiom(assumption: Term, analysisSourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType, description: Option[String]): Option[Int] = None
  override def createLabelNode(labelTerm: Var, sourceChunks: Iterable[Chunk], sourceTerms: Iterable[Term]): Option[LabelNode] = None

  override def createAssertOrCheckNode(term: Term, assumptionType: AssumptionType, analysisSourceInfo: AnalysisSourceInfo, isCheck: Boolean): Option[GeneralAssertionNode] = None
  override def addAssertFalseNode(isCheck: Boolean, assumptionType: AssumptionType, sourceInfo: AnalysisSourceInfo): Option[Int] = None
  override def addInfeasibilityNode(isCheck: Boolean, sourceInfo: AnalysisSourceInfo): Option[Int] = None

  override def addDependency(source: Option[Int], dest: Option[Int]): Unit = {}
  override def processUnsatCoreAndAddDependencies(dep: String, assertionLabel: String): Unit = {}
  override def addPermissionDependencies(sourceChunks: Set[Chunk], sourceTerms: Set[Term], targetChunk: Chunk): Unit = {}
  override def addCustomTransitiveDependency(sourceSourceInfo: AnalysisSourceInfo, targetSourceInfo: AnalysisSourceInfo): Unit = {}
  override def addDependenciesForExplicitPostconditions(sourceExps: Seq[ast.Exp], targetExps: Seq[ast.Exp]): Unit = {}
  override def addFunctionAxiomEdges(): Unit = {}

  override def buildFinalGraph(): Option[DependencyGraph] = None
}