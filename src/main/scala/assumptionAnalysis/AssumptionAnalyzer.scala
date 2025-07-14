package viper.silicon.assumptionAnalysis

import viper.silicon.assumptionAnalysis.AssumptionType.AssumptionType
import viper.silicon.interfaces.state.{Chunk, GeneralChunk}
import viper.silicon.state.terms._
import viper.silicon.verifier.Verifier
import viper.silver.ast


trait AssumptionAnalyzer {
  val assumptionGraph: AssumptionAnalysisGraph = new DefaultAssumptionAnalysisGraph()
  protected var isClosed_ = false
  protected var infeasibilityNode: Option[Int] = None

  def disableTransitiveEdges(): Unit = {
    isClosed_ = true
  }

  def enableTransitiveEdges(): Unit = {
    isClosed_ = false
  }

  def getinfeasibilityNode: Option[Int] = infeasibilityNode

  def setinfeasibilityNode(nodeId: Int): Unit = {
    infeasibilityNode = Some(nodeId)
  }

  def unsetinfeasibilityNode(): Unit = {
    infeasibilityNode = None
  }

  def getNodes: Iterable[AssumptionAnalysisNode]
  def getChunkInhaleNode(chunk: Chunk): Option[PermissionInhaleNode] = None

  def addNodes(nodes: Iterable[AssumptionAnalysisNode]): Unit
  def addNode(node: AssumptionAnalysisNode): Unit
  def addAssumption(assumption: Term, analysisSourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType, description: Option[String] = None): Option[Int]
  def addPermissionExhaleNode(chunk: Chunk, permAmount: Term, sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Option[Int]

  def createAssertOrCheckNode(term: Term, assumptionType: AssumptionType, analysisSourceInfo: AnalysisSourceInfo, isCheck: Boolean): Option[GeneralAssertionNode]
  def addAssertFalseNode(isCheck: Boolean, assumptionType: AssumptionType, sourceInfo: AnalysisSourceInfo): Option[Int]
  def addInfeasibilityNode(isCheck: Boolean, sourceInfo: AnalysisSourceInfo): Option[Int] = None

  def addDependency(source: Option[Int], dest: Option[Int]): Unit
  def processUnsatCoreAndAddDependencies(dep: String, assertionLabel: String): Unit
  def addPermissionDependencies(sourceChunks: Set[Chunk], sourceTerms: Set[Term], targetChunk: Chunk): Unit
  def addDependencyFromExhaleToInhale(inhaledChunk: Chunk, sourceInfo: AnalysisSourceInfo): Unit
  def addCustomTransitiveDependency(sourceSourceInfo: AnalysisSourceInfo, targetSourceInfo: AnalysisSourceInfo): Unit = {}

  def getMember: Option[ast.Member]

  def exportGraph(): Unit

  def createLabelNode(labelTerm: Term, sourceChunks: Iterable[Chunk], sourceTerms: Iterable[Term]): Option[LabelNode] = None
  def registerInhaleChunk[CH <: GeneralChunk](sourceChunks: Set[Chunk], buildChunk: (Term => CH), perm: Term, labelNode: Option[LabelNode], analysisInfo: AnalysisInfo, isExhale: Boolean): CH = buildChunk(perm)
  def registerExhaleChunk[CH <: GeneralChunk](sourceChunks: Set[Chunk], buildChunk: (Term => CH), perm: Term, analysisInfo: AnalysisInfo): CH = buildChunk(perm)

  def computeProofCoverage(): Unit = {}

  def exportMergedGraph(): Unit = {
    if(Verifier.config.assumptionAnalysisExportPath.isEmpty) return

    val mergedGraph = assumptionGraph.mergeNodesBySource()

    val foldername: Option[String] = getMember map {
      case ast.Method(name, _, _, _, _, _) => name
      case ast.Function(name, _, _, _, _, _) => name
      case ast.Domain(name, _, _, _, _) => name
      case contracted: ast.Contracted => contracted.toString()
      case location: ast.Location => location.pos.toString
      case member: ast.ExtensionMember => member.pos.toString
    }
    mergedGraph.exportGraph(Verifier.config.assumptionAnalysisExportPath() + "/" + foldername.getOrElse("latestExport") + "_merged")
  }

}

object AssumptionAnalyzer {
  val assumptionTypeAnnotationKey = "assumptionType"
  val enableAssumptionAnalysisAnnotationKey = "enableAssumptionAnalysis"

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

  def createEnableAnalysisInfo(enableAnalysis: Boolean): ast.AnnotationInfo =
    ast.AnnotationInfo(Map((enableAssumptionAnalysisAnnotationKey, Seq(enableAnalysis.toString))))

  def createAnalysisAnnotationInfo(enableAnalysis: Boolean, assumptionType: AssumptionType): ast.AnnotationInfo =
    ast.AnnotationInfo(Map(
      (enableAssumptionAnalysisAnnotationKey, Seq(enableAnalysis.toString)),
      (assumptionTypeAnnotationKey, Seq(assumptionType.toString))
    ))

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

  def joinGraphs(assumptionAnalysisGraphs: Set[AssumptionAnalysisGraph]): AssumptionAnalysisGraph = {
    val newGraph = new DefaultAssumptionAnalysisGraph
    assumptionAnalysisGraphs foreach (graph => newGraph.addNodes(graph.nodes))
    assumptionAnalysisGraphs foreach (graph => graph.edges foreach {case (s, t) => newGraph.addEdges(s, t)})
    assumptionAnalysisGraphs foreach (graph => graph.transitiveEdges foreach {case (s, t) => newGraph.addEdges(s, t)})
    val types = Set(AssumptionType.Implicit, AssumptionType.Explicit)
    val relevantAssumptionNodes = newGraph.nodes filter (node => node.isInstanceOf[GeneralAssumptionNode] && types.contains(node.assumptionType))
    newGraph.nodes filter (node => node.isInstanceOf[GeneralAssertionNode] && node.assumptionType.equals(AssumptionType.Postcondition)) foreach {node =>
      val nodeSourceInfoString = node.sourceInfo.getTopLevelSource.toString
      val assumptionNodesForJoin = relevantAssumptionNodes filter (aNode => aNode.sourceInfo.getFineGrainedSource.toString.equals(nodeSourceInfoString))
      newGraph.addEdges(node.id, assumptionNodesForJoin map (_.id))
    }
    newGraph
  }

}

class DefaultAssumptionAnalyzer(member: ast.Member) extends AssumptionAnalyzer {
  protected var originalLabelNodes: List[LabelNode] = List.empty
  protected var proofCoverage: Double = 0.0

  override def addNodes(nodes: Iterable[AssumptionAnalysisNode]): Unit = {
    assumptionGraph.addNodes(nodes)
  }

  override def getNodes: Iterable[AssumptionAnalysisNode] = assumptionGraph.nodes

  override def addNode(node: AssumptionAnalysisNode): Unit = {
    assumptionGraph.addNode(node)
  }

  override def addAssumption(assumption: Term, analysisSourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType, description: Option[String]): Option[Int] = {
    val node = SimpleAssumptionNode(assumption, description, analysisSourceInfo, assumptionType, isClosed_)
    addNode(node)
    Some(node.id)
  }

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

  private def addPermissionInhaleNode(chunk: Chunk, permAmount: Term, sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType, labelNode: LabelNode): Option[Int] = {
    val node = PermissionInhaleNode(chunk, permAmount, sourceInfo, assumptionType, isClosed_, labelNode)
    addNode(node)
    Some(node.id)
  }

  override def addPermissionExhaleNode(chunk: Chunk, permAmount: Term, sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Option[Int] = {
    val node = PermissionExhaleNode(chunk, permAmount, sourceInfo, assumptionType, isClosed_)
    addNode(node)
    addPermissionDependencies(Set(chunk), Set(), Some(node.id))
    Some(node.id)
  }

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

  private def getChunkNodeIdsWithSource(oldChunks: Set[Chunk], sourceInfo: AnalysisSourceInfo): Set[Int] = {
    assumptionGraph.nodes
      .filter(c => c.isInstanceOf[PermissionInhaleNode] && oldChunks.contains(c.asInstanceOf[ChunkAnalysisInfo].getChunk) && c.sourceInfo.equals(sourceInfo))
      .map(_.id).toSet
  }

  private def getNodeIdsByTerm(terms: Set[Term]): Set[Int] = {
    assumptionGraph.nodes
      .filter(t => terms.contains(t.getTerm))
      .map(_.id).toSet
  }

  override def addDependencyFromExhaleToInhale(inhaledChunk: Chunk, sourceInfo: AnalysisSourceInfo): Unit = {
    val inhaledChunkNodeIds = getChunkNodeIdsWithSource(Set(inhaledChunk), sourceInfo)
    assert(inhaledChunkNodeIds.size == 1)
    val exhaleNodes = assumptionGraph.nodes
      .filter(c => c.isInstanceOf[PermissionExhaleNode] && c.sourceInfo.equals(sourceInfo))
      .map(_.id).toSet
    assumptionGraph.addEdges(exhaleNodes, inhaledChunkNodeIds)
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

  override def addDependency(source: Option[Int], dest: Option[Int]): Unit = {
    if(source.isDefined && dest.isDefined)
      assumptionGraph.addEdges(source.get, Set(dest.get))
  }

  override def addCustomTransitiveDependency(sourceSourceInfo: AnalysisSourceInfo, targetSourceInfo: AnalysisSourceInfo): Unit = {
    val sourceNodes = assumptionGraph.nodes filter (n => n.isInstanceOf[GeneralAssertionNode] && n.sourceInfo.getSourceForTransitiveEdges.equals(sourceSourceInfo.getSourceForTransitiveEdges))
    val targetNodes = assumptionGraph.nodes filter (n => n.isInstanceOf[GeneralAssumptionNode] && n.sourceInfo.getSourceForTransitiveEdges.equals(targetSourceInfo.getSourceForTransitiveEdges))
    assumptionGraph.addEdges(sourceNodes map (_.id), targetNodes map (_.id))
  }

  override def getMember: Option[ast.Member] = Some(member)

  override def exportGraph(): Unit = {
    if(Verifier.config.assumptionAnalysisExportPath.isEmpty) return

    val foldername: Option[String] = getMember map {
      case ast.Method(name, _, _, _, _, _) => name
      case ast.Function(name, _, _, _, _, _) => name
      case ast.Domain(name, _, _, _, _) => name
      case contracted: ast.Contracted => contracted.toString()
      case location: ast.Location => location.pos.toString
      case member: ast.ExtensionMember => member.pos.toString
    }
    assumptionGraph.exportGraph(Verifier.config.assumptionAnalysisExportPath() + "/" + foldername.getOrElse("latestExport"))
  }


  override def createLabelNode(labelTerm: Term, sourceChunks: Iterable[Chunk], sourceTerms: Iterable[Term]): Option[LabelNode] = {
    val labelNode = LabelNode(labelTerm)
    addNode(labelNode)
    originalLabelNodes = originalLabelNodes :+ labelNode
    assumptionGraph.addEdges(getChunkNodeIds(sourceChunks.toSet) ++ getNodeIdsByTerm(sourceTerms.toSet), labelNode.id)
    Some(labelNode)
  }

  override def registerExhaleChunk[CH <: GeneralChunk](sourceChunks: Set[Chunk], buildChunk: (Term => CH), perm: Term, analysisInfo: AnalysisInfo): CH = {
    val chunk = buildChunk(perm)
    val chunkNode = addPermissionExhaleNode(chunk, chunk.perm, analysisInfo.sourceInfo, analysisInfo.assumptionType)
    addPermissionDependencies(sourceChunks, Set(), chunkNode)
    chunk
  }

  override def registerInhaleChunk[CH <: GeneralChunk](sourceChunks: Set[Chunk], buildChunk: (Term => CH), perm: Term, labelNodeOpt: Option[LabelNode], analysisInfo: AnalysisInfo, isExhale: Boolean): CH = {
    val labelNode = labelNodeOpt.get
    val chunk = buildChunk(Ite(labelNode.term, perm, NoPerm))
    val chunkNode = addPermissionInhaleNode(chunk, chunk.perm, analysisInfo.sourceInfo, analysisInfo.assumptionType, labelNode)
    if(chunkNode.isDefined)
      addDependency(chunkNode, Some(labelNode.id))
    addPermissionDependencies(sourceChunks, Set(), chunkNode)
    chunk
  }

  override def computeProofCoverage(): Unit = {
    val explicitAssertionNodes = assumptionGraph.getExplicitAssertionNodes
    val explicitAssertionNodeIds = explicitAssertionNodes map (_.id)
    val nodesPerSourceInfo = assumptionGraph.getNonInternalAssumptionNodesPerSource
    val coveredNodes = nodesPerSourceInfo filter { case (_, nodes) =>
      val nodeIds = (nodes map (_.id)).toSet
      // it is either an explicit assertion itself or it has a dependency to an explicit assertion
      nodeIds.intersect(explicitAssertionNodeIds).nonEmpty ||
        assumptionGraph.existsAnyDependency(nodeIds, explicitAssertionNodeIds)
    }
    proofCoverage = coveredNodes.size.toDouble / nodesPerSourceInfo.size.toDouble
  }
}

class NoAssumptionAnalyzer extends AssumptionAnalyzer {

  override def getNodes: Iterable[AssumptionAnalysisNode] = Seq()
  override def addNode(node: AssumptionAnalysisNode): Unit = {}
  override def addNodes(nodes: Iterable[AssumptionAnalysisNode]): Unit = {}
  override def createAssertOrCheckNode(term: Term, assumptionType: AssumptionType, analysisSourceInfo: AnalysisSourceInfo, isCheck: Boolean): Option[GeneralAssertionNode] = None

  override def addInfeasibilityNode(isCheck: Boolean, sourceInfo: AnalysisSourceInfo): Option[Int] = None
  override def processUnsatCoreAndAddDependencies(dep: String, assertionLabel: String): Unit = {
  }

  override def addPermissionExhaleNode(chunk: Chunk, permAmount: Term, sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Option[Int] = None

  override def addDependencyFromExhaleToInhale(inhaledChunk: Chunk, sourceInfo: AnalysisSourceInfo): Unit = {}

  override def addPermissionDependencies(sourceChunks: Set[Chunk], sourceTerms: Set[Term], newChunkNodeId: Chunk): Unit = {}
  def addDependency(source: Option[Int], dest: Option[Int]): Unit = {}
  override def getMember: Option[ast.Member] = None

  override def addAssumption(term: Term, analysisSourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType, description: Option[String]): Option[Int] = None
  override def exportGraph(): Unit = {}

  override def addAssertFalseNode(isCheck: Boolean, assumptionType: AssumptionType, sourceInfo: AnalysisSourceInfo): Option[Int] = None
}