package viper.silicon.dependencyAnalysis

import viper.silicon.dependencyAnalysis.AssumptionType.AssumptionType
import viper.silicon.interfaces.state.{Chunk, GeneralChunk}
import viper.silicon.state.terms._
import viper.silicon.verifier.Verifier
import viper.silver.ast

import java.util.concurrent.atomic.AtomicLong
import scala.collection.mutable


trait DependencyAnalyzer {
  protected val assumptionGraph: DependencyGraph = new DependencyGraph()
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
  def addCustomExpDependency(sourceExps: Seq[ast.Exp], targetExps: Seq[ast.Exp]): Unit
  def addFunctionAxiomEdges(): Unit

  def  addInfeasibilityDepToStmt(infeasNodeId: Option[Int], analysisSourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Unit = {}

  def buildFinalGraph(): Option[DependencyGraph]
}

object DependencyAnalyzer {
  val analysisLabelName: String = "$$analysisLabel$$"
  private val assumptionTypeAnnotationKey = "assumptionType"
  private val enableDependencyAnalysisAnnotationKey = "enableDependencyAnalysis"
  val timeToVerifyAndCollectDependencies: AtomicLong = new AtomicLong(0)
  val timeToVerifyAndBuildFinalGraph: AtomicLong = new AtomicLong(0)
  val timeToAddNodes: AtomicLong = new AtomicLong(0)
  val timeToAddEdges: AtomicLong = new AtomicLong(0)
  val timeToExtractCandidateNodes: AtomicLong = new AtomicLong(0)

  def startTimeMeasurement(): Long = {
    if(!Verifier.config.enableDependencyAnalysisProfiling()) return 0
    System.nanoTime()
  }

  def stopTimeMeasurementAndAddToTotal(startTime: Long, total: AtomicLong): Unit = {
    if(!Verifier.config.enableDependencyAnalysisProfiling()) return

    val endTime = System.nanoTime()
    total.addAndGet(endTime - startTime)
  }

  def printProfilingResults(): Unit = {
    if(!Verifier.config.enableDependencyAnalysisProfiling()) return
    println(s"Overall runtime = time spent on verification and building the final graph: ${timeToVerifyAndBuildFinalGraph.get() / 1e6}ms")
    println(s"This runtime can be categorized into the following, fine-grained measurements.")
    println(s"  Time spent on verification and collecting low-level dependencies: ${timeToVerifyAndCollectDependencies.get() / 1e6}ms")
    println(s"  Time spent on adding nodes: ${timeToAddNodes.get() / 1e6}ms")
    println(s"  Time spent on adding edges: ${timeToAddEdges.get() / 1e6}ms")
    println(s"  Time spent on extracting candidate nodes: ${timeToExtractCandidateNodes.get() / 1e6}ms")
  }

  private def extractAnnotationFromInfo(info: ast.Info, annotationKey: String): Option[Seq[String]] = {
    info.getAllInfos[ast.AnnotationInfo]
      .filter(_.values.contains(annotationKey))
      .map(_.values(annotationKey)).headOption
  }

  def extractAssumptionTypeFromInfo(info: ast.Info): Option[AssumptionType] = {
    val annotation = extractAnnotationFromInfo(info, assumptionTypeAnnotationKey)
    if(annotation.isDefined && annotation.get.nonEmpty) AssumptionType.fromString(annotation.get.head) else None
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

  // TODO ake: implement a lazy join in DependencyGraphInterpreter
  def joinGraphsAndGetInterpreter(name: Option[String], dependencyGraphInterpreters: Set[DependencyGraphInterpreter]): DependencyGraphInterpreter = {

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

    // axioms assumed by every method / function should depend on the assertions that justify them
    // hence, we add edges from function postconditions & bodies to the corresponding axioms
    val axiomAssertionNodes = joinCandidateNodes
      .filter(n => (n.isInstanceOf[GeneralAssertionNode] && AssumptionType.postconditionTypes.contains(n.assumptionType))
      || AssumptionType.FunctionBody.equals(n.assumptionType))
      .groupBy(_.sourceInfo.getTopLevelSource.toString)
      .view.mapValues(_.map(_.id))
      .toMap
    joinCandidateNodes.filter(_.isInstanceOf[AxiomAssumptionNode])
      .groupBy(n => n.sourceInfo.toString)
      .map{case (sourceInfo, axiomNodes) => (axiomNodes.map(_.id), axiomAssertionNodes.getOrElse(sourceInfo, Seq.empty))}
      .foreach{case (axiomNodeIds, assertionNodeIds) =>
        newGraph.addEdges(assertionNodeIds, axiomNodeIds) // TODO ake: maybe we could merge the axiom nodes here since they represent the same axiom?
    }

    // postconditions of methods assumed by every method call should depend on the assertions that justify them
    // hence, we add edges from assertions of method postconditions to assumptions of the same postcondition (at method calls)
    val relevantAssumptionNodes = joinCandidateNodes
      .filter(node => node.isInstanceOf[GeneralAssumptionNode] && AssumptionType.postconditionTypes.contains(node.assumptionType))
      .groupBy(_.sourceInfo.getFineGrainedSource.toString)
      .view.mapValues(_.map(_.id))
      .toMap
    joinCandidateNodes.filter(node => node.isInstanceOf[GeneralAssertionNode] && AssumptionType.postconditionTypes.contains(node.assumptionType))
      .map(node => (node.id, relevantAssumptionNodes.getOrElse(node.sourceInfo.getTopLevelSource.toString, Seq.empty)))
      .foreach { case (src, targets) => newGraph.addEdges(src, targets)}

    val newInterpreter = new DependencyGraphInterpreter(name.getOrElse("joined"), newGraph)
    newInterpreter
  }
}

class DefaultDependencyAnalyzer(member: ast.Member) extends DependencyAnalyzer {
  protected var proofCoverage: Double = 0.0

  override def getMember: Option[ast.Member] = Some(member)

  override def getNodes: Iterable[DependencyAnalysisNode] = assumptionGraph.nodes

  override def getChunkInhaleNode(chunk: Chunk): Option[PermissionInhaleNode] = {
    val inhaleNode = assumptionGraph.nodes
      .filter(c => c.isInstanceOf[PermissionInhaleNode] && chunk.equals(c.asInstanceOf[ChunkAnalysisInfo].getChunk))
      .map(_.asInstanceOf[PermissionInhaleNode])
    assert(inhaleNode.size == 1)
    inhaleNode.headOption
  }

  private def getChunkNodeIds(oldChunks: Set[Chunk]): Set[Int] = {
    assumptionGraph.nodes
      .filter(c => c.isInstanceOf[PermissionInhaleNode] && oldChunks.contains(c.asInstanceOf[ChunkAnalysisInfo].getChunk))
      .map(_.id).toSet
  }

  private def getNodeIdsByTerm(terms: Set[Term]): Set[Int] = {
    assumptionGraph.nodes
      .filter(t => terms.contains(t.getTerm))
      .map(_.id).toSet
  }


  override def addNodes(nodes: Iterable[DependencyAnalysisNode]): Unit = {
    assumptionGraph.addNodes(nodes)
  }

  override def addNode(node: DependencyAnalysisNode): Unit = {
    assumptionGraph.addNode(node)
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
    val chunk = buildChunk(perm)
    val chunkNode = addPermissionExhaleNode(chunk, chunk.perm, analysisInfo.sourceInfo, analysisInfo.assumptionType)
    addPermissionDependencies(sourceChunks, Set(), chunkNode)
    chunk
  }

  override def registerInhaleChunk[CH <: GeneralChunk](sourceChunks: Set[Chunk], buildChunk: Term => CH, perm: Term, labelNodeOpt: Option[LabelNode], analysisInfo: AnalysisInfo, isExhale: Boolean): CH = {
    val labelNode = labelNodeOpt.get
    val chunk = buildChunk(Ite(labelNode.term, perm, NoPerm))
    val chunkNode = addPermissionInhaleNode(chunk, chunk.perm, analysisInfo.sourceInfo, analysisInfo.assumptionType, labelNode)
    if(chunkNode.isDefined)
      addDependency(chunkNode, Some(labelNode.id))
    addPermissionDependencies(sourceChunks, Set(), chunkNode)
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
    assumptionGraph.addEdges(getChunkNodeIds(sourceChunks.toSet) ++ getNodeIdsByTerm(sourceTerms.toSet), labelNode.id)
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
      assumptionGraph.addEdges(source.get, Set(dest.get))
  }

  override def processUnsatCoreAndAddDependencies(dep: String, assertionLabel: String): Unit = {
    val assumptionLabels = dep.replace("(", "").replace(")", "").split(" ")
    val assumptionIds = assumptionLabels.filter(DependencyAnalyzer.isAssumptionLabel).map(DependencyAnalyzer.getIdFromLabel)
    val assertionIdsFromUnsatCore = assumptionLabels.filter(DependencyAnalyzer.isAssertionLabel).map(DependencyAnalyzer.getIdFromLabel)
    val assertionIdFromLabel = DependencyAnalyzer.getIdFromLabel(assertionLabel)
    val assertionIds = assertionIdFromLabel +: assertionIdsFromUnsatCore
    assumptionGraph.addEdges(assumptionIds, assertionIds)
    val axiomIds = assumptionLabels.filter(DependencyAnalyzer.isAxiomLabel).map(DependencyAnalyzer.getIdFromLabel)
    assumptionGraph.addEdges(axiomIds, assertionIds)
  }

  private def addPermissionDependencies(sourceChunks: Set[Chunk], sourceTerms: Set[Term], newChunkNodeId: Option[Int]): Unit = {
    if(newChunkNodeId.isEmpty) return

    val sourceNodeIds = getChunkNodeIds(sourceChunks).filter(id => id != newChunkNodeId.get) ++ getNodeIdsByTerm(sourceTerms)
    assumptionGraph.addEdges(sourceNodeIds, newChunkNodeId.get)
  }

  override def addPermissionDependencies(sourceChunks: Set[Chunk], sourceTerms: Set[Term], newChunk: Chunk): Unit = {
    val newChunkId = assumptionGraph.nodes
      .filter(c => c.isInstanceOf[PermissionInhaleNode] && c.isInstanceOf[ChunkAnalysisInfo] && newChunk.equals(c.asInstanceOf[ChunkAnalysisInfo].getChunk))
      .map(_.id).toSet
    addPermissionDependencies(sourceChunks, sourceTerms, newChunkId.headOption)
  }

  override def addCustomTransitiveDependency(sourceSourceInfo: AnalysisSourceInfo, targetSourceInfo: AnalysisSourceInfo): Unit = {
    val sourceNodes = assumptionGraph.nodes filter (n => n.isInstanceOf[GeneralAssertionNode] && n.sourceInfo.getSourceForTransitiveEdges.equals(sourceSourceInfo.getSourceForTransitiveEdges))
    val targetNodes = assumptionGraph.nodes filter (n => n.isInstanceOf[GeneralAssumptionNode] && n.sourceInfo.getSourceForTransitiveEdges.equals(targetSourceInfo.getSourceForTransitiveEdges))
    assumptionGraph.addEdges(sourceNodes map (_.id), targetNodes map (_.id))
  }

  def addCustomExpDependency(sourceExps: Seq[ast.Exp], targetExps: Seq[ast.Exp]): Unit = {
    val sourceNodeIds = sourceExps.flatMap(e => addAssumption(True, ExpAnalysisSourceInfo(e), AssumptionType.Explicit, None))
    val targetNodes = targetExps.flatMap(e => addAssertNode(True, AssumptionType.ExplicitPostcondition, ExpAnalysisSourceInfo(e)))
    assumptionGraph.addEdges(sourceNodeIds, targetNodes)
  }

  override def buildFinalGraph(): Option[DependencyGraph] = {
    assumptionGraph.removeLabelNodes()
    val mergedGraph = if(Verifier.config.enableDependencyAnalysisDebugging()) assumptionGraph else  buildAndGetMergedGraph()
    mergedGraph.addTransitiveEdges()
    Some(mergedGraph)
  }

  override def addFunctionAxiomEdges(): Unit = {
    val axiomNodes = getNodes.filter(_.isInstanceOf[AxiomAssumptionNode])
    val postcondNodes = getNodes.filter(n => n.assumptionType.equals(AssumptionType.ExplicitPostcondition) || n.assumptionType.equals(AssumptionType.ImplicitPostcondition))
    axiomNodes foreach {aNode =>
      val pNodes = postcondNodes filter (_.sourceInfo.toString.equals(aNode.sourceInfo.toString)) map (_.id)
      assumptionGraph.addEdges(pNodes, aNode.id)
    }
  }

  private def buildAndGetMergedGraph(): DependencyGraph = {
    def keepNode(n: DependencyAnalysisNode): Boolean = n.isClosed || n.isInstanceOf[InfeasibilityNode] || n.isInstanceOf[AxiomAssumptionNode]

    val mergedGraph = new DependencyGraph
    val nodeMap = mutable.HashMap[Int, Int]()
    assumptionGraph.getNodes.filter(keepNode).foreach { n =>
      nodeMap.put(n.id, n.id)
      mergedGraph.addNode(n)
    }

    val nodesBySource = assumptionGraph.getNodes.filter(!keepNode(_))
      .groupBy(n => (n.sourceInfo.getSourceForTransitiveEdges.toString, n.sourceInfo.getTopLevelSource.toString, n.sourceInfo.getFineGrainedSource, n.assumptionType))

    nodesBySource foreach { case ((_, _, _, assumptionType), nodes) =>
      val assumptionNodes = nodes.filter(_.isInstanceOf[GeneralAssumptionNode])
      if (assumptionNodes.nonEmpty) {
        val newNode = SimpleAssumptionNode(True, None, assumptionNodes.head.sourceInfo, assumptionType, isClosed = false)
        assumptionNodes foreach (n => nodeMap.put(n.id, newNode.id))
        mergedGraph.addNode(newNode)
      }
    }

    nodesBySource foreach { case ((_, _, _, assumptionType), nodes) =>
      val assertionNodes = nodes.filter(_.isInstanceOf[GeneralAssertionNode])
      if (assertionNodes.nonEmpty) {
        val newNode = SimpleAssertionNode(True, assumptionType, assertionNodes.head.sourceInfo, isClosed = false)
        assertionNodes foreach (n => nodeMap.put(n.id, newNode.id))
        mergedGraph.addNode(newNode)
      }
    }

    assumptionGraph.getAllEdges foreach { case (target, deps) =>
      val newTarget = nodeMap(target)
      mergedGraph.addEdges(deps.map(nodeMap(_)), newTarget)
    }

    mergedGraph
  }

  override def addInfeasibilityDepToStmt(infeasNodeId: Option[Int], analysisSourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Unit = {
    val newAssertionNodeId = addAssertNode(False, assumptionType, analysisSourceInfo)
    val newAssumptionNodeId = addAssumption(False, analysisSourceInfo, assumptionType)
    addDependency(infeasNodeId, newAssumptionNodeId)
    addDependency(infeasNodeId, newAssertionNodeId)
  }
}

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
  override def addCustomExpDependency(sourceExps: Seq[ast.Exp], targetExps: Seq[ast.Exp]): Unit = {}
  override def addFunctionAxiomEdges(): Unit = {}

  override def buildFinalGraph(): Option[DependencyGraph] = None
}