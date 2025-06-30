package viper.silicon.assumptionAnalysis

import viper.silicon.assumptionAnalysis.AssumptionType.AssumptionType
import viper.silicon.interfaces.state.{Chunk, GeneralChunk}
import viper.silicon.state.terms._
import viper.silicon.verifier.Verifier
import viper.silver.ast


trait AssumptionAnalyzer {
  val assumptionGraph: AssumptionAnalysisGraph = new DefaultAssumptionAnalysisGraph()
  protected var isClosed_ = false

  def disableTransitiveEdges(): Unit = {
    isClosed_ = true
  }

  def enableTransitiveEdges(): Unit = {
    isClosed_ = false
  }

  def addPermissionInhaleNode(chunk: Chunk, permAmount: Term, sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Option[Int]
  def addPermissionAssertNode(chunk: Chunk, permAmount: Term, sourceInfo: AnalysisSourceInfo): Option[Int]
  def addPermissionExhaleNode(chunk: Chunk, permAmount: Term, sourceInfo: AnalysisSourceInfo): Option[Int]
  def addPermissionNode(chunk: Chunk, permAmount: Term, sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType = AssumptionType.Explicit, isExhale: Boolean=false): Option[Int]
  def addNodes(nodes: Iterable[AssumptionAnalysisNode]): Unit
  def addNode(node: AssumptionAnalysisNode): Unit
  def getNodes: Iterable[AssumptionAnalysisNode]

  def addAssumption(assumption: Term, analysisSourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType, description: Option[String] = None): Option[Int]

  def createAssertOrCheckNode(term: Term, assertion: Either[String, ast.Exp], analysisSourceInfo: AnalysisSourceInfo, isCheck: Boolean): Option[GeneralAssertionNode]

  def getChunkNodeIds(oldChunks: Set[Chunk]): Set[Int]
  def getNodeIdsByTerm(terms: Set[Term]): Set[Int]
  def addDependencyFromExhaleToInhale(inhaledChunk: Chunk, sourceInfo: AnalysisSourceInfo): Unit
  def addPermissionDependencies(oldChunks: Set[Chunk], newChunkNodeId: Option[Int]): Unit
  def addPermissionDependencies(oldChunks: Set[Chunk], newChunkNodeId: Chunk): Unit
  def addDependency(source: Int, dest: Int): Unit

  def processUnsatCoreAndAddDependencies(dep: String, assertionLabel: String): Unit

  def addAssertFalseNode(isCheck: Boolean, sourceInfo: AnalysisSourceInfo): Option[Int]

  def getMember: Option[ast.Member]

  def exportGraph(): Unit

  def createLabelNode(labelTerm: Term, sourceChunks: Iterable[Chunk], sourceTerms: Iterable[Term]): LabelNode = LabelNode(True)
  def registerDerivedChunk[CH <: GeneralChunk](sourceChunk: CH, buildChunk: (Term => CH), perm: Term, labelNode: LabelNode, analysisInfo: AnalysisInfo, isExhale: Boolean, createLabel: Boolean=true): CH = buildChunk(perm)
  def registerChunk[CH <: GeneralChunk](buildChunk: (Term => CH), perm: Term, labelNode: LabelNode, analysisInfo: AnalysisInfo, isExhale: Boolean): CH = buildChunk(perm)
  def getReassumeLabelNodes: Iterable[LabelNode] = Set.empty
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


  def createAssumptionLabel(id: Option[Int], offset: Int = 0): String = {
    createLabel("assumption", id, offset)
  }

  def createAssertionLabel(id: Option[Int], offset: Int = 0): String = {
    createLabel("assertion", id, offset)
  }

  def createAxiomLabel(id: Option[Int]): String = {
    createLabel("axiom", id)
  }

  private def createLabel(description: String, id: Option[Int], offset: Int = 0): String = {
    if (id.isDefined) description + "_" + id.get + "_" + offset
    else ""
  }

  def getIdFromLabel(label: String): Int = {
    label.split("_")(1).toInt
  }

  def isAssertionLabel(label: String): Boolean = label.startsWith("assertion_")

  def isAssumptionLabel(label: String): Boolean = label.startsWith("assumption_")

  def isAxiomLabel(label: String): Boolean = label.startsWith("axiom_")
}

class DefaultAssumptionAnalyzer(member: ast.Member) extends AssumptionAnalyzer {
  protected var originalLabelNodes: List[LabelNode] = List.empty

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

  override def createAssertOrCheckNode(term: Term, assertion: Either[String, ast.Exp], analysisSourceInfo: AnalysisSourceInfo, isCheck: Boolean): Option[GeneralAssertionNode] = {
    if(isCheck) return Some(SimpleCheckNode(term, analysisSourceInfo, isClosed_))

    Some(assertion match {
      case Left(description) => StringAssertionNode(description, term, analysisSourceInfo, isClosed_)
      case Right(exp) => SimpleAssertionNode(exp, term, analysisSourceInfo, isClosed_)
    })
  }

  override def addAssertFalseNode(isCheck: Boolean, sourceInfo: AnalysisSourceInfo): Option[Int] = {
    val node = createAssertOrCheckNode(False, Right(ast.FalseLit()()), sourceInfo, isCheck)
    addNode(node.get)
    node.map(_.id)
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

  override def addPermissionInhaleNode(chunk: Chunk, permAmount: Term, sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Option[Int] = {
    val node = PermissionInhaleNode(chunk, permAmount, sourceInfo, assumptionType, isClosed_)
    addNode(node)
    Some(node.id)
  }

  override def addPermissionAssertNode(chunk: Chunk, permAmount: Term, sourceInfo: AnalysisSourceInfo): Option[Int] = {
    val node = PermissionAssertNode(chunk, permAmount, sourceInfo, isClosed_)
    addNode(node)
    addPermissionDependencies(Set(chunk), Some(node.id))
    Some(node.id)
  }

  override def addPermissionExhaleNode(chunk: Chunk, permAmount: Term, sourceInfo: AnalysisSourceInfo): Option[Int] = {
    val node = PermissionExhaleNode(chunk, permAmount, sourceInfo, isClosed_)
    addNode(node)
    addPermissionDependencies(Set(chunk), Some(node.id))
    Some(node.id)
  }

  override def addPermissionNode(chunk: Chunk, permAmount: Term, sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType = AssumptionType.Explicit, isExhale: Boolean=false): Option[Int] = {
    if(isExhale) addPermissionExhaleNode(chunk, permAmount, sourceInfo)
    else addPermissionInhaleNode(chunk, permAmount, sourceInfo, assumptionType)
  }

  override def getChunkNodeIds(oldChunks: Set[Chunk]): Set[Int] = {
    assumptionGraph.nodes
      .filter(c => c.isInstanceOf[PermissionInhaleNode] && oldChunks.contains(c.asInstanceOf[ChunkAnalysisInfo].getChunk))
      .map(_.id).toSet
  }

  private def getChunkNodeIdsWithSource(oldChunks: Set[Chunk], sourceInfo: AnalysisSourceInfo): Set[Int] = {
    assumptionGraph.nodes
      .filter(c => c.isInstanceOf[PermissionInhaleNode] && oldChunks.contains(c.asInstanceOf[ChunkAnalysisInfo].getChunk) && c.sourceInfo.equals(sourceInfo))
      .map(_.id).toSet
  }

  override def getNodeIdsByTerm(terms: Set[Term]): Set[Int] = {
    assumptionGraph.nodes
      .filter(t => terms.contains(t.getTerm))
      .map(_.id).toSet
  }

  override def addDependencyFromExhaleToInhale(inhaledChunk: Chunk, sourceInfo: AnalysisSourceInfo): Unit = {
    val inhaledChunkNodeIds = getChunkNodeIdsWithSource(Set(inhaledChunk), sourceInfo)
    assert(inhaledChunkNodeIds.size == 1)
    val exhaleNodes = assumptionGraph.nodes
      .filter(c => c.isInstanceOf[PermissionExhaleNode] && c.isClosed && c.sourceInfo.equals(sourceInfo))
      .map(_.id).toSet
    assumptionGraph.addEdges(exhaleNodes, inhaledChunkNodeIds)
  }

  override def addPermissionDependencies(oldChunks: Set[Chunk], newChunkNodeId: Option[Int]): Unit = {
    if(newChunkNodeId.isEmpty) return

    val oldChunkNodeIds = getChunkNodeIds(oldChunks).filter(id => id != newChunkNodeId.get)
    assumptionGraph.addEdges(oldChunkNodeIds, newChunkNodeId.get)
  }

  override def addPermissionDependencies(oldChunks: Set[Chunk], newChunk: Chunk): Unit = {
    val newChunkId = assumptionGraph.nodes
      .filter(c => c.isInstanceOf[PermissionInhaleNode] && c.isInstanceOf[ChunkAnalysisInfo] && newChunk.equals(c.asInstanceOf[ChunkAnalysisInfo].getChunk))
      .map(_.id).toSet
    addPermissionDependencies(oldChunks, newChunkId.headOption)
  }

  override def addDependency(source: Int, dest: Int): Unit = {
    assumptionGraph.addEdges(source, Set(dest))
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


  override def createLabelNode(labelTerm: Term, sourceChunks: Iterable[Chunk], sourceTerms: Iterable[Term]): LabelNode = {
    val labelNode = LabelNode(labelTerm)
    addNode(labelNode)
    originalLabelNodes = originalLabelNodes :+ labelNode
    assumptionGraph.addEdges(getChunkNodeIds(sourceChunks.toSet) ++ getNodeIdsByTerm(sourceTerms.toSet), labelNode.id)
    labelNode
  }

  override def registerChunk[CH <: GeneralChunk](buildChunk: (Term => CH), perm: Term, labelNode: LabelNode, analysisInfo: AnalysisInfo, isExhale: Boolean): CH = {
    val chunk = if(isExhale) buildChunk(perm) else buildChunk(Ite(labelNode.term, perm, NoPerm))
    val chunkNode = addPermissionNode(chunk, chunk.perm, analysisInfo.sourceInfo, analysisInfo.assumptionType, isExhale)
    if(chunkNode.isDefined)
      addDependency(chunkNode.get, labelNode.id)
    chunk
  }

  override def registerDerivedChunk[CH <: GeneralChunk](sourceChunk: CH, buildChunk: (Term => CH), perm: Term, labelNode: LabelNode, analysisInfo: AnalysisInfo, isExhale: Boolean, createLabel: Boolean=true): CH = {
    val chunk = if(isExhale) buildChunk(perm) else buildChunk(Ite(labelNode.term, perm, NoPerm))
    val chunkNode = addPermissionNode(chunk, chunk.perm, analysisInfo.sourceInfo, analysisInfo.assumptionType, isExhale)
    if(chunkNode.isDefined)
      addDependency(chunkNode.get, labelNode.id)
    addPermissionDependencies(Set(sourceChunk), chunkNode)
    chunk
  }



  private def createReassumeLabelNode(oldLabelNode: LabelNode): LabelNode = {
    val newLabelNode = LabelNode(oldLabelNode.term)
    // do not add to originalLabelNodes!
    addNode(newLabelNode)
    assumptionGraph.addEdges(Set(oldLabelNode.id), newLabelNode.id)
    newLabelNode
  }

  override def getReassumeLabelNodes: Iterable[LabelNode] = { // TODO ake: work with scopes!
    originalLabelNodes map createReassumeLabelNode
  }
}

class NoAssumptionAnalyzer extends AssumptionAnalyzer {

  override def getNodes: Iterable[AssumptionAnalysisNode] = Seq()
  override def addNode(node: AssumptionAnalysisNode): Unit = {}
  override def addNodes(nodes: Iterable[AssumptionAnalysisNode]): Unit = {}
  override def createAssertOrCheckNode(term: Term, assertion: Either[String, ast.Exp], analysisSourceInfo: AnalysisSourceInfo, isCheck: Boolean): Option[GeneralAssertionNode] = None

  override def addAssertFalseNode(isCheck: Boolean, sourceInfo: AnalysisSourceInfo): Option[Int] = None
  override def processUnsatCoreAndAddDependencies(dep: String, assertionLabel: String): Unit = {
  }

  override def addPermissionInhaleNode(chunk: Chunk, permAmount: Term, sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Option[Int] = None
  override def addPermissionExhaleNode(chunk: Chunk, permAmount: Term, sourceInfo: AnalysisSourceInfo): Option[Int] = None
  override def addPermissionAssertNode(chunk: Chunk, permAmount: Term, sourceInfo: AnalysisSourceInfo): Option[Int] = None
  override def addPermissionNode(chunk: Chunk, permAmount: Term, sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType, isExhale: Boolean=false): Option[Int] = None


  override def getChunkNodeIds(oldChunks: Set[Chunk]): Set[Int] = Set.empty
  override def getNodeIdsByTerm(terms: Set[Term]): Set[Int] = Set.empty

  override def addDependencyFromExhaleToInhale(inhaledChunk: Chunk, sourceInfo: AnalysisSourceInfo): Unit = {}
  override def addPermissionDependencies(oldChunks: Set[Chunk], newChunkNode: Option[Int]): Unit = {
  }

  override def addPermissionDependencies(oldChunks: Set[Chunk], newChunkNodeId: Chunk): Unit = {}
  def addDependency(source: Int, dest: Int): Unit = {}
  override def getMember: Option[ast.Member] = None

  override def addAssumption(term: Term, analysisSourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType, description: Option[String]): Option[Int] = None
  override def exportGraph(): Unit = {}
}