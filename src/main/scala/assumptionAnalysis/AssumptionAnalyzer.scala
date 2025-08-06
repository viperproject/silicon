package viper.silicon.assumptionAnalysis

import viper.silicon.assumptionAnalysis.AssumptionType.AssumptionType
import viper.silicon.interfaces.state.{Chunk, GeneralChunk}
import viper.silicon.state.terms._
import viper.silver.ast

import scala.collection.mutable


trait AssumptionAnalyzer {
  protected val assumptionGraph: AssumptionAnalysisGraph = new AssumptionAnalysisGraph()
  protected var isClosed_ = false

  def disableTransitiveEdges(): Unit = {
    isClosed_ = true
  }

  def enableTransitiveEdges(): Unit = {
    isClosed_ = false
  }

  def getMember: Option[ast.Member]

  def getNodes: Iterable[AssumptionAnalysisNode]
  def getChunkInhaleNode(chunk: Chunk): Option[PermissionInhaleNode]

  def addNodes(nodes: Iterable[AssumptionAnalysisNode]): Unit
  def addNode(node: AssumptionAnalysisNode): Unit
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

  def buildFinalGraph(): Option[AssumptionAnalysisGraph]
}

object AssumptionAnalyzer {
  val analysisLabelName: String = "$$analysisLabel$$"
  private val assumptionTypeAnnotationKey = "assumptionType"
  private val enableAssumptionAnalysisAnnotationKey = "enableAssumptionAnalysis"

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
    val annotation = extractAnnotationFromInfo(info, enableAssumptionAnalysisAnnotationKey)
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

  def joinGraphsAndGetInterpreter(name: Option[String], assumptionAnalysisInterpreters: Set[AssumptionAnalysisInterpreter]): AssumptionAnalysisInterpreter = {
    val newGraph = new AssumptionAnalysisGraph

    assumptionAnalysisInterpreters foreach (interpreter => newGraph.addNodes(interpreter.getGraph.getNodes))
    assumptionAnalysisInterpreters foreach (interpreter => interpreter.getGraph.getAllEdges foreach {case (t, deps) => newGraph.addEdges(deps, t)})

    // add edges between identical axioms since they were added to each interpreter // TODO ake: merge instead?
    newGraph.getNodes.filter(_.isInstanceOf[AxiomAssumptionNode]).groupBy(n => (n.sourceInfo.toString, n.assumptionType)).foreach{case (_, nodes) =>
      newGraph.addEdges(nodes.map(_.id), nodes.map(_.id))
    }

    val types = Set(AssumptionType.Implicit, AssumptionType.Explicit)
    val relevantAssumptionNodes = newGraph.nodes filter (node => node.isInstanceOf[GeneralAssumptionNode] && types.contains(node.assumptionType))

    newGraph.nodes filter (node => AssumptionType.postconditionTypes.contains(node.assumptionType)) foreach { node =>
      val nodeSourceInfoString = node.sourceInfo.getTopLevelSource.toString
      val assumptionNodesForJoin = relevantAssumptionNodes filter (aNode => aNode.sourceInfo.getFineGrainedSource.toString.equals(nodeSourceInfoString))
      newGraph.addEdges(node.id, assumptionNodesForJoin map (_.id))
    }

    new AssumptionAnalysisInterpreter(name.getOrElse("joined"), newGraph)
  }
}

class DefaultAssumptionAnalyzer(member: ast.Member) extends AssumptionAnalyzer {
  protected var proofCoverage: Double = 0.0

  override def getMember: Option[ast.Member] = Some(member)

  override def getNodes: Iterable[AssumptionAnalysisNode] = assumptionGraph.nodes

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


  override def addNodes(nodes: Iterable[AssumptionAnalysisNode]): Unit = {
    assumptionGraph.addNodes(nodes)
  }

  override def addNode(node: AssumptionAnalysisNode): Unit = {
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
    val assumptionIds = assumptionLabels.filter(AssumptionAnalyzer.isAssumptionLabel).map(AssumptionAnalyzer.getIdFromLabel)
    val assertionIdsFromUnsatCore = assumptionLabels.filter(AssumptionAnalyzer.isAssertionLabel).map(AssumptionAnalyzer.getIdFromLabel)
    val assertionIdFromLabel = AssumptionAnalyzer.getIdFromLabel(assertionLabel)
    val assertionIds = assertionIdFromLabel +: assertionIdsFromUnsatCore
    assumptionGraph.addEdges(assumptionIds, assertionIds)
    val axiomIds = assumptionLabels.filter(AssumptionAnalyzer.isAxiomLabel).map(AssumptionAnalyzer.getIdFromLabel)
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
    val targetNodes = targetExps.flatMap(e => addAssumption(True, ExpAnalysisSourceInfo(e), AssumptionType.ExplicitPostcondition, None))
    assumptionGraph.addEdges(sourceNodeIds, targetNodes)
  }

  override def buildFinalGraph(): Option[AssumptionAnalysisGraph] = {
    assumptionGraph.removeLabelNodes()
    val mergedGraph = buildAndGetMergedGraph()
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

  private def buildAndGetMergedGraph(): AssumptionAnalysisGraph = {
    def keepNode(n: AssumptionAnalysisNode): Boolean = n.isClosed || n.isInstanceOf[InfeasibilityNode] || n.isInstanceOf[AxiomAssumptionNode]

    val mergedGraph = new AssumptionAnalysisGraph
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
}

class NoAssumptionAnalyzer extends AssumptionAnalyzer {

  override def getMember: Option[ast.Member] = None

  override def getNodes: Iterable[AssumptionAnalysisNode] = Set.empty
  override def getChunkInhaleNode(chunk: Chunk): Option[PermissionInhaleNode] = None

  override def addNodes(nodes: Iterable[AssumptionAnalysisNode]): Unit = {}
  override def addNode(node: AssumptionAnalysisNode): Unit = {}
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

  override def buildFinalGraph(): Option[AssumptionAnalysisGraph] = None
}