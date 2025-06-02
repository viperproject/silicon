package viper.silicon.assumptionAnalysis

import viper.silicon.assumptionAnalysis.AssumptionType.AssumptionType
import viper.silicon.debugger.DebugExp
import viper.silicon.interfaces.state.Chunk
import viper.silicon.state.terms.Term
import viper.silver.ast
import viper.silver.ast._


trait AssumptionAnalyzer {
  val assumptionGraph: AssumptionAnalysisGraph = new DefaultAssumptionAnalysisGraph()

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

  def addPermissionDependencies(oldChunks: Set[Chunk], newChunkNodeId: Option[Int]): Unit
  def addPermissionDependencies(oldChunks: Set[Chunk], newChunkNodeId: Chunk): Unit

  def processUnsatCoreAndAddDependencies(dep: String, assertionLabel: String): Unit

  protected var sourceInfoes: List[AnalysisSourceInfo] = List.empty
  protected var forcedMainSource: Option[AnalysisSourceInfo] = None

  def getAnalysisInfo: AnalysisInfo = getAnalysisInfo(AssumptionType.Implicit)

  def getAnalysisInfo(assumptionType: AssumptionType): AnalysisInfo = AnalysisInfo(this, getFullSourceInfo, assumptionType)

  def getFullSourceInfo: AnalysisSourceInfo = {
    if(forcedMainSource.isDefined)
      return forcedMainSource.get
    if(sourceInfoes.size <= 1){
      sourceInfoes.headOption.getOrElse(NoAnalysisSourceInfo())
    } else{
      CompositeAnalysisSourceInfo(sourceInfoes.last, sourceInfoes.head)
    }
  }

  def addAnalysisSourceInfo(analysisSourceInfo: AnalysisSourceInfo): AnalysisSourceInfo = {
    sourceInfoes = analysisSourceInfo +: sourceInfoes
    analysisSourceInfo
  }

  def popAnalysisSourceInfo(): Unit = {
    sourceInfoes = sourceInfoes.tail
    forcedMainSource = None
  }

  def setForcedSource(description: String): Unit = {
    forcedMainSource = Some(StringAnalysisSourceInfo(description, getFullSourceInfo.getPosition))
  }

  def setForcedSource(source: AnalysisSourceInfo): Unit = {
    forcedMainSource = Some(source)
  }

  def unsetForcedSource(): Unit = {
    forcedMainSource = None
  }

  def getAnalysisSourceInfoes: List[AnalysisSourceInfo] = sourceInfoes
  def setAnalysisSourceInfoes(infoes: List[AnalysisSourceInfo]): Unit = {
    sourceInfoes = infoes
  }

  def addAnalysisSourceInfo(e: ast.Exp): Unit = {
    sourceInfoes = ExpAnalysisSourceInfo(e) +: sourceInfoes
  }

  def getMember: Option[Member]

  def exportGraph(): Unit

}

object AssumptionAnalyzer {
  val assumptionTypeAnnotationKey = "assumptionType"
  val enableAssumptionAnalysisAnnotationKey = "enableAssumptionAnalysis"
  val noAssumptionAnalyzerSingelton = new NoAssumptionAnalyzer()

  private def extractAnnotationFromInfo(info: Info, annotationKey: String): Option[Seq[String]] = {
    info.getAllInfos[AnnotationInfo]
      .filter(_.values.contains(annotationKey))
      .map(_.values(annotationKey)).headOption
  }

  def extractAssumptionTypeFromInfo(info: Info): Option[AssumptionType] = {
    val annotation = extractAnnotationFromInfo(info, assumptionTypeAnnotationKey)
    if(annotation.isDefined && annotation.get.nonEmpty) AssumptionType.fromString(annotation.get.head) else None
  }


  def extractEnableAnalysisFromInfo(info: Info): Option[Boolean] = {
    val annotation = extractAnnotationFromInfo(info, enableAssumptionAnalysisAnnotationKey)
    if(annotation.isDefined && annotation.get.nonEmpty) annotation.get.head.toBooleanOption else None
  }

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

class DefaultAssumptionAnalyzer(member: Member) extends AssumptionAnalyzer {

  override def addNodes(nodes: Iterable[AssumptionAnalysisNode]): Unit = {
    assumptionGraph.addNodes(nodes)
  }

  override def getNodes: Iterable[AssumptionAnalysisNode] = assumptionGraph.nodes

  override def addNode(node: AssumptionAnalysisNode): Unit = {
    assumptionGraph.addNode(node)
  }

  override def addSingleAssumption(assumption: DebugExp, analysisSourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Option[Int] = {
    val node = if(assumption.originalExp.isDefined) SimpleAssumptionNode(assumption.originalExp.get, analysisSourceInfo, assumptionType)
    else StringAssumptionNode(assumption.description.getOrElse("unknown"), analysisSourceInfo, assumptionType)
    addNode(node)
    Some(node.id)
  }


  override def addAssumption(assumption: ast.Exp, analysisSourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Option[Int] = {
    val node = SimpleAssumptionNode(assumption, analysisSourceInfo, assumptionType)
    addNode(node)
    Some(node.id)
  }


  override def addAssumption(assumption: String, analysisSourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Option[Int] = {
    val node = StringAssumptionNode(assumption, analysisSourceInfo, assumptionType)
    addNode(node)
    Some(node.id)
  }

  override def addAssumptions(assumptions: Iterable[DebugExp], analysisSourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Seq[Int] = {
    val newNodes = assumptions.toSeq.map(a =>
      if (a.originalExp.isDefined) SimpleAssumptionNode(a.originalExp.get, if(analysisSourceInfo.isInstanceOf[NoAnalysisSourceInfo]) ExpAnalysisSourceInfo(a.originalExp.get) else analysisSourceInfo, assumptionType)
      else StringAssumptionNode(a.description.getOrElse("unknown"), analysisSourceInfo, AssumptionType.Internal)
    )
    newNodes foreach addNode
    newNodes.map(_.id).toSeq
  }

  override def createAssertOrCheckNode(term: Term, assertion: Either[String, ast.Exp], analysisSourceInfo: AnalysisSourceInfo, isCheck: Boolean): Option[GeneralAssertionNode] = {
    if(isCheck) return Some(SimpleCheckNode(term, analysisSourceInfo))

    Some(assertion match {
      case Left(description) => StringAssertionNode(description, analysisSourceInfo)
      case Right(exp) => SimpleAssertionNode(exp, analysisSourceInfo)
    })
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
    val node = PermissionInhaleNode(chunk, permAmount, sourceInfo, assumptionType)
    addNode(node)
    Some(node.id)
  }

  override def addPermissionAssertNode(chunk: Chunk, permAmount: Option[ast.Exp], sourceInfo: AnalysisSourceInfo): Option[Int] = {
    val node = PermissionAssertNode(chunk, permAmount, sourceInfo)
    addNode(node)
    addPermissionDependencies(Set(chunk), Some(node.id))
    Some(node.id)
  }

  override def addPermissionExhaleNode(chunk: Chunk, permAmount: Option[ast.Exp], sourceInfo: AnalysisSourceInfo): Option[Int] = {
    val node = PermissionExhaleNode(chunk, permAmount, sourceInfo)
    addNode(node)
    addPermissionDependencies(Set(chunk), Some(node.id))
    Some(node.id)
  }

  override def addPermissionNode(chunk: Chunk, permAmount: Option[Exp], sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType = AssumptionType.Explicit, isExhale: Boolean=false): Option[Int] = {
    if(isExhale) addPermissionExhaleNode(chunk, permAmount, sourceInfo)
    else addPermissionInhaleNode(chunk, permAmount, sourceInfo, assumptionType)
  }

  override def addPermissionDependencies(oldChunks: Set[Chunk], newChunkNodeId: Option[Int]): Unit = {
    if(newChunkNodeId.isEmpty) return

    val oldChunkNodeIds = assumptionGraph.nodes
      .filter(c => c.id != newChunkNodeId.get && c.isInstanceOf[PermissionInhaleNode] && oldChunks.contains(c.asInstanceOf[ChunkAnalysisInfo].getChunk))
      .map(_.id).toSet
    assumptionGraph.addEdges(oldChunkNodeIds, newChunkNodeId.get)
  }

  override def addPermissionDependencies(oldChunks: Set[Chunk], newChunk: Chunk): Unit = {
    val newChunkId = assumptionGraph.nodes
      .filter(c => c.isInstanceOf[PermissionInhaleNode] && c.isInstanceOf[ChunkAnalysisInfo] && newChunk.equals(c.asInstanceOf[ChunkAnalysisInfo].getChunk))
      .map(_.id).toSet
    addPermissionDependencies(oldChunks, newChunkId.headOption)
  }

  override def getMember: Option[Member] = Some(member)

  override def exportGraph(): Unit = {
    val foldername: Option[String] = getMember map {
      case Method(name, _, _, _, _, _) => name
      case ast.Function(name, _, _, _, _, _) => name
      case Domain(name, _, _, _, _) => name
      case contracted: Contracted => contracted.toString()
      case location: Location => location.pos.toString
      case member: ExtensionMember => member.pos.toString
    }
    assumptionGraph.exportGraph("graphExports/" + foldername.getOrElse("latestExport"))
  }

}

class NoAssumptionAnalyzer extends AssumptionAnalyzer {

  override def getNodes: Iterable[AssumptionAnalysisNode] = Seq()
  override def addNode(node: AssumptionAnalysisNode): Unit = {}
  override def addNodes(nodes: Iterable[AssumptionAnalysisNode]): Unit = {}

  override def addAssumptions(assumptions: Iterable[DebugExp], analysisSourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Seq[Int] = Seq.empty

  override def createAssertOrCheckNode(term: Term, assertion: Either[String, ast.Exp], analysisSourceInfo: AnalysisSourceInfo, isCheck: Boolean): Option[GeneralAssertionNode] = None

  override def processUnsatCoreAndAddDependencies(dep: String, assertionLabel: String): Unit = {
  }

  override def addPermissionInhaleNode(chunk: Chunk, permAmount: Option[ast.Exp], sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Option[Int] = None
  override def addPermissionExhaleNode(chunk: Chunk, permAmount: Option[ast.Exp], sourceInfo: AnalysisSourceInfo): Option[Int] = None
  override def addPermissionAssertNode(chunk: Chunk, permAmount: Option[ast.Exp], sourceInfo: AnalysisSourceInfo): Option[Int] = None
  override def addPermissionNode(chunk: Chunk, permAmount: Option[ast.Exp], sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType, isExhale: Boolean=false): Option[Int] = None

  override def addPermissionDependencies(oldChunks: Set[Chunk], newChunkNode: Option[Int]): Unit = {
  }

  override def addPermissionDependencies(oldChunks: Set[Chunk], newChunkNodeId: Chunk): Unit = {}

  override def getMember: Option[Member] = None

  override def addSingleAssumption(assumption: DebugExp, analysisSourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Option[Int] = None

  override def addAssumption(assumption: ast.Exp, analysisSourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Option[Int] = None

  override def addAssumption(assumption: String, analysisSourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Option[Int] = None
  override def exportGraph(): Unit = {}
}