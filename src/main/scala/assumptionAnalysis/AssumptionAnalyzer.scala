package viper.silicon.assumptionAnalysis

import viper.silicon.assumptionAnalysis.AssumptionType.AssumptionType
import viper.silicon.debugger.DebugExp
import viper.silicon.decider.Decider
import viper.silicon.interfaces.state.Chunk
import viper.silicon.state.terms.{False, Ite, Term, True}
import viper.silver.ast


trait AssumptionAnalyzer {
  val assumptionGraph: AssumptionAnalysisGraph = new DefaultAssumptionAnalysisGraph()
  var forcedDependencies: List[Int] = List.empty
  protected var enableCustomEdges_ = false

  def enableCustomEdges(): Unit = {
    enableCustomEdges_ = true
  }

  def disableCustomEdges(): Unit = {
    enableCustomEdges_ = false
  }

  def addPermissionInhaleNode(chunk: Chunk, permAmount: Option[ast.Exp], sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Option[Int]
  def addPermissionAssertNode(chunk: Chunk, permAmount: Option[ast.Exp], sourceInfo: AnalysisSourceInfo): Option[Int]
  def addPermissionExhaleNode(chunk: Chunk, permAmount: Option[ast.Exp], sourceInfo: AnalysisSourceInfo): Option[Int]
  def addPermissionNode(chunk: Chunk, permAmount: Option[ast.Exp], sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType = AssumptionType.Explicit, isExhale: Boolean=false): Option[Int]
  def addNodes(nodes: Iterable[AssumptionAnalysisNode]): Unit
  def addNode(node: AssumptionAnalysisNode): Unit
  def getNodes: Iterable[AssumptionAnalysisNode]

  def addSingleAssumption(assumption: DebugExp, analysisSourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Option[Int]

  def addAssumptions(assumptions: Iterable[DebugExp], analysisSourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Seq[Int]
  def addAssumption(assumption: ast.Exp, analysisSourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Option[Int]
  def addAssumption(assumption: String, analysisSourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Option[Int]

  def createAssertOrCheckNode(term: Term, assertion: Either[String, ast.Exp], analysisSourceInfo: AnalysisSourceInfo, isCheck: Boolean): Option[GeneralAssertionNode]

  def getChunkNodeIds(oldChunks: Set[Chunk]): Set[Int]
  def addDependencyFromExhaleToInhale(newChunkNodeId: Option[Int]): Unit
  def addPermissionDependencies(oldChunks: Set[Chunk], newChunkNodeId: Option[Int]): Unit
  def addPermissionDependencies(oldChunks: Set[Chunk], newChunkNodeId: Chunk): Unit

  def processUnsatCoreAndAddDependencies(dep: String, assertionLabel: String): Unit

  def addAssertFalseNode(isCheck: Boolean, sourceInfo: AnalysisSourceInfo): Option[Int]

  def getMember: Option[ast.Member]

  def exportGraph(): Unit

  def addForcedDependencies(chunks: Set[Chunk]): Unit = {
    forcedDependencies = forcedDependencies ++ getChunkNodeIds(chunks).toList
  }

  def unsetForcedDependencies(): Unit = {
    forcedDependencies = List.empty
  }

  def createLabelledConditional(decider: Decider, sourceChunks: Iterable[Chunk], thenTerm: Term, elseTerm: Term): Term

}

object AssumptionAnalyzer {
  val assumptionTypeAnnotationKey = "assumptionType"
  val enableAssumptionAnalysisAnnotationKey = "enableAssumptionAnalysis"
  val noAssumptionAnalyzerSingelton = new NoAssumptionAnalyzer()

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

  override def addNodes(nodes: Iterable[AssumptionAnalysisNode]): Unit = {
    assumptionGraph.addNodes(nodes)
    assumptionGraph.addEdges(forcedDependencies, nodes.map(_.id))
  }

  override def getNodes: Iterable[AssumptionAnalysisNode] = assumptionGraph.nodes

  override def addNode(node: AssumptionAnalysisNode): Unit = {
    assumptionGraph.addNode(node)
    assumptionGraph.addEdges(forcedDependencies, node.id)
  }

  override def addSingleAssumption(assumption: DebugExp, analysisSourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Option[Int] = {
    val node = if(assumption.originalExp.isDefined) SimpleAssumptionNode(assumption.originalExp.get, analysisSourceInfo, AssumptionAnalyzer.extractAssumptionTypeFromInfo(assumption.originalExp.get.info).getOrElse(assumptionType), enableCustomEdges_)
    else StringAssumptionNode(assumption.description.getOrElse("unknown"), analysisSourceInfo, assumptionType, enableCustomEdges_)
    addNode(node)
    Some(node.id)
  }


  override def addAssumption(assumption: ast.Exp, analysisSourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Option[Int] = {
    val node = SimpleAssumptionNode(assumption, analysisSourceInfo, AssumptionAnalyzer.extractAssumptionTypeFromInfo(assumption.info).getOrElse(assumptionType), enableCustomEdges_)
    addNode(node)
    Some(node.id)
  }


  override def addAssumption(assumption: String, analysisSourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Option[Int] = {
    val node = StringAssumptionNode(assumption, analysisSourceInfo, assumptionType, enableCustomEdges_)
    addNode(node)
    Some(node.id)
  }

  override def addAssumptions(assumptions: Iterable[DebugExp], analysisSourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Seq[Int] = {
    val newNodes = assumptions.toSeq.map(a =>
      if (a.originalExp.isDefined) SimpleAssumptionNode(a.originalExp.get, if(analysisSourceInfo.isInstanceOf[NoAnalysisSourceInfo]) ExpAnalysisSourceInfo(a.originalExp.get) else analysisSourceInfo,
        AssumptionAnalyzer.extractAssumptionTypeFromInfo(a.originalExp.get.info).getOrElse(assumptionType), enableCustomEdges_)
      else StringAssumptionNode(a.description.getOrElse("unknown"), analysisSourceInfo, AssumptionType.Internal, enableCustomEdges_)
    )
    newNodes foreach addNode
    newNodes.map(_.id)
  }

  override def createAssertOrCheckNode(term: Term, assertion: Either[String, ast.Exp], analysisSourceInfo: AnalysisSourceInfo, isCheck: Boolean): Option[GeneralAssertionNode] = {
    if(isCheck) return Some(SimpleCheckNode(term, analysisSourceInfo, enableCustomEdges_))

    Some(assertion match {
      case Left(description) => StringAssertionNode(description, analysisSourceInfo, enableCustomEdges_)
      case Right(exp) => SimpleAssertionNode(exp, analysisSourceInfo, enableCustomEdges_)
    })
  }

  override def addAssertFalseNode(isCheck: Boolean, sourceInfo: AnalysisSourceInfo): Option[Int] = {
    val node = createAssertOrCheckNode(False, Right(ast.FalseLit()()), sourceInfo, isCheck)
    addNode(node.get)
    node.map(_.id)
  }

  override def processUnsatCoreAndAddDependencies(dep: String, assertionLabel: String): Unit = {
    val assumptionLabels = dep.replace("(", "").replace(")", "").split(" ")
    if(assumptionLabels.size < 2) return
    val assumptionIds = assumptionLabels.filter(AssumptionAnalyzer.isAssumptionLabel).map(AssumptionAnalyzer.getIdFromLabel)
    val assertionIdsFromUnsatCore = assumptionLabels.filter(AssumptionAnalyzer.isAssertionLabel).map(AssumptionAnalyzer.getIdFromLabel)
    val assertionIdFromLabel = AssumptionAnalyzer.getIdFromLabel(assertionLabel)
    val assertionIds = assertionIdFromLabel +: assertionIdsFromUnsatCore // TODO ake: add check (not already contained)
    assumptionGraph.addEdges(assumptionIds, assertionIds)
    val axiomIds = assumptionLabels.filter(AssumptionAnalyzer.isAxiomLabel).map(AssumptionAnalyzer.getIdFromLabel)
    assumptionGraph.addEdges(axiomIds, assertionIds)
  }

  override def addPermissionInhaleNode(chunk: Chunk, permAmount: Option[ast.Exp], sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Option[Int] = {
    val node = PermissionInhaleNode(chunk, permAmount, sourceInfo, assumptionType, enableCustomEdges_)
    addNode(node)
    Some(node.id)
  }

  override def addPermissionAssertNode(chunk: Chunk, permAmount: Option[ast.Exp], sourceInfo: AnalysisSourceInfo): Option[Int] = {
    val node = PermissionAssertNode(chunk, permAmount, sourceInfo, enableCustomEdges_)
    addNode(node)
    addPermissionDependencies(Set(chunk), Some(node.id))
    Some(node.id)
  }

  override def addPermissionExhaleNode(chunk: Chunk, permAmount: Option[ast.Exp], sourceInfo: AnalysisSourceInfo): Option[Int] = {
    val node = PermissionExhaleNode(chunk, permAmount, sourceInfo, enableCustomEdges_)
    addNode(node)
    addPermissionDependencies(Set(chunk), Some(node.id))
    Some(node.id)
  }

  override def addPermissionNode(chunk: Chunk, permAmount: Option[ast.Exp], sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType = AssumptionType.Explicit, isExhale: Boolean=false): Option[Int] = {
    if(isExhale) addPermissionExhaleNode(chunk, permAmount, sourceInfo)
    else addPermissionInhaleNode(chunk, permAmount, sourceInfo, assumptionType)
  }

  override def getChunkNodeIds(oldChunks: Set[Chunk]): Set[Int] = {
    assumptionGraph.nodes
      .filter(c => c.isInstanceOf[PermissionInhaleNode] && oldChunks.contains(c.asInstanceOf[ChunkAnalysisInfo].getChunk))
      .map(_.id).toSet
  }

  override def addDependencyFromExhaleToInhale(newChunkNodeId: Option[Int]): Unit = {
    if(newChunkNodeId.isEmpty) return
    val newChunkNode = assumptionGraph.nodes.filter(_.id == newChunkNodeId.get).head
    val exhaleNodes = assumptionGraph.nodes
      .filter(c => c.isInstanceOf[PermissionExhaleNode] && c.isClosed && c.sourceInfo.equals(newChunkNode.sourceInfo))
      .map(_.id).toSet
    assumptionGraph.addEdges(exhaleNodes, newChunkNodeId)
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

  override def getMember: Option[ast.Member] = Some(member)

  override def exportGraph(): Unit = {
    val foldername: Option[String] = getMember map {
      case ast.Method(name, _, _, _, _, _) => name
      case ast.Function(name, _, _, _, _, _) => name
      case ast.Domain(name, _, _, _, _) => name
      case contracted: ast.Contracted => contracted.toString()
      case location: ast.Location => location.pos.toString
      case member: ast.ExtensionMember => member.pos.toString
    }
    assumptionGraph.exportGraph("graphExports/" + foldername.getOrElse("latestExport"))
  }

  override def createLabelledConditional(decider: Decider, sourceChunks: Iterable[Chunk], thenTerm: Term, elseTerm: Term): Term = {
    val savedForcedDep = forcedDependencies
    addForcedDependencies(sourceChunks.toSet)
    val (label, labelExp) = decider.fresh(ast.LocalVar("analysisLabel", ast.Bool)())
    decider.assume(label === True, Some(DebugExp.createInstance(labelExp, labelExp)), AssumptionType.Internal)
    forcedDependencies = savedForcedDep
    Ite(label === True, thenTerm, elseTerm)
  }

}

class NoAssumptionAnalyzer extends AssumptionAnalyzer {

  override def getNodes: Iterable[AssumptionAnalysisNode] = Seq()
  override def addNode(node: AssumptionAnalysisNode): Unit = {}
  override def addNodes(nodes: Iterable[AssumptionAnalysisNode]): Unit = {}

  override def addAssumptions(assumptions: Iterable[DebugExp], analysisSourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Seq[Int] = Seq.empty

  override def createAssertOrCheckNode(term: Term, assertion: Either[String, ast.Exp], analysisSourceInfo: AnalysisSourceInfo, isCheck: Boolean): Option[GeneralAssertionNode] = None

  override def addAssertFalseNode(isCheck: Boolean, sourceInfo: AnalysisSourceInfo): Option[Int] = None
  override def processUnsatCoreAndAddDependencies(dep: String, assertionLabel: String): Unit = {
  }

  override def addPermissionInhaleNode(chunk: Chunk, permAmount: Option[ast.Exp], sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Option[Int] = None
  override def addPermissionExhaleNode(chunk: Chunk, permAmount: Option[ast.Exp], sourceInfo: AnalysisSourceInfo): Option[Int] = None
  override def addPermissionAssertNode(chunk: Chunk, permAmount: Option[ast.Exp], sourceInfo: AnalysisSourceInfo): Option[Int] = None
  override def addPermissionNode(chunk: Chunk, permAmount: Option[ast.Exp], sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType, isExhale: Boolean=false): Option[Int] = None


  override def getChunkNodeIds(oldChunks: Set[Chunk]): Set[Int] = Set.empty

  override def addDependencyFromExhaleToInhale(newChunkNodeId: Option[Int]): Unit = {}
  override def addPermissionDependencies(oldChunks: Set[Chunk], newChunkNode: Option[Int]): Unit = {
  }

  override def addPermissionDependencies(oldChunks: Set[Chunk], newChunkNodeId: Chunk): Unit = {}

  override def getMember: Option[ast.Member] = None

  override def addSingleAssumption(assumption: DebugExp, analysisSourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Option[Int] = None

  override def addAssumption(assumption: ast.Exp, analysisSourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Option[Int] = None

  override def addAssumption(assumption: String, analysisSourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Option[Int] = None
  override def exportGraph(): Unit = {}

  override def createLabelledConditional(decider: Decider, sourceChunks: Iterable[Chunk], thenTerm: Term, elseTerm: Term): Term = thenTerm
}