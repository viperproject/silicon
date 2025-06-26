package viper.silicon.assumptionAnalysis

import viper.silicon.assumptionAnalysis.AssumptionType.AssumptionType
import viper.silicon.debugger.DebugExp
import viper.silicon.decider.Decider
import viper.silicon.interfaces.state.Chunk
import viper.silicon.state.terms.{False, Implies, Ite, NoPerm, Term, True}
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
  def addAssumption(assumption: ast.Exp, term: Term, analysisSourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Option[Int]
  def addAssumption(assumption: String, term: Term, analysisSourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Option[Int]

  def createAssertOrCheckNode(term: Term, assertion: Either[String, ast.Exp], analysisSourceInfo: AnalysisSourceInfo, isCheck: Boolean): Option[GeneralAssertionNode]

  def getChunkNodeIds(oldChunks: Set[Chunk]): Set[Int]
  def getNodeIds(terms: Set[Term]): Set[Int]
  def addDependencyFromExhaleToInhale(newChunkNodeId: Option[Int]): Unit
  def addPermissionDependencies(oldChunks: Set[Chunk], newChunkNodeId: Option[Int]): Unit
  def addPermissionDependencies(oldChunks: Set[Chunk], newChunkNodeId: Chunk): Unit

  def processUnsatCoreAndAddDependencies(dep: String, assertionLabel: String): Unit

  def addAssertFalseNode(isCheck: Boolean, sourceInfo: AnalysisSourceInfo): Option[Int]

  def getMember: Option[ast.Member]

  def exportGraph(): Unit

  def addForcedDependencies(ids: Set[Int]): Unit = {
    forcedDependencies = forcedDependencies ++ ids
  }

  def addForcedChunkDependencies(chunks: Set[Chunk]): Unit = {
    addForcedDependencies(getChunkNodeIds(chunks))
  }

  def unsetForcedDependencies(): Unit = {
    forcedDependencies = List.empty
  }

  def wrapWithLabel(labelNode: LabelNode, term: Term): Term = term
  def wrapPermissionWithLabel(labelNode: LabelNode, term: Term): Term = term
  def createAndAssumeLabelNode(decider: Decider, sourceNodeIds: Iterable[Int]): LabelNode = LabelNode(True)
  def createLabelledConditionalChunks(decider: Decider, sourceChunks: Iterable[Chunk], thenTerm: Term, elseTerm: Term): Term = thenTerm
  def createLabelledConditionalChunks(decider: Decider, sourceChunks: Iterable[Chunk], thenTerm: Term): Term = thenTerm
  def createLabelledConditional(decider: Decider, sourceTerms: Iterable[Term], term: Term): Term = term
  def createLabelledConditional(decider: Decider, sourceTerms: Iterable[Term], terms: Seq[Term]): Seq[Term] = terms
  def reassumeLabels(decider: Decider): Unit = {}

  def createLabelledConditional(decider: Decider, sourceNodeId: Int, term: Term): Term = term

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
  protected var originalLabelNodes: List[LabelNode] = List.empty

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
    val node =
      if(assumption.originalExp.isDefined) SimpleAssumptionNode(assumption.originalExp.get, assumption.term.getOrElse(True) /* TODO ake */, analysisSourceInfo, AssumptionAnalyzer.extractAssumptionTypeFromInfo(assumption.originalExp.get.info).getOrElse(assumptionType), enableCustomEdges_)
      else StringAssumptionNode(assumption.description.getOrElse("unknown"), assumption.term.getOrElse(True) /* TODO ake */, analysisSourceInfo, assumptionType, enableCustomEdges_)
    addNode(node)
    Some(node.id)
  }


  override def addAssumption(assumption: ast.Exp, term: Term, analysisSourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Option[Int] = {
    val node = SimpleAssumptionNode(assumption, term, analysisSourceInfo, AssumptionAnalyzer.extractAssumptionTypeFromInfo(assumption.info).getOrElse(assumptionType), enableCustomEdges_)
    addNode(node)
    Some(node.id)
  }


  override def addAssumption(assumption: String, term: Term, analysisSourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Option[Int] = {
    val node = StringAssumptionNode(assumption, term, analysisSourceInfo, assumptionType, enableCustomEdges_)
    addNode(node)
    Some(node.id)
  }

  override def addAssumptions(assumptions: Iterable[DebugExp], analysisSourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Seq[Int] = {
    val newNodes = assumptions.toSeq.map(a =>
      if (a.originalExp.isDefined) SimpleAssumptionNode(a.originalExp.get, a.term.getOrElse(True)  /* TODO ake */, if(analysisSourceInfo.isInstanceOf[NoAnalysisSourceInfo]) ExpAnalysisSourceInfo(a.originalExp.get) else analysisSourceInfo,
        AssumptionAnalyzer.extractAssumptionTypeFromInfo(a.originalExp.get.info).getOrElse(assumptionType), enableCustomEdges_)
      else StringAssumptionNode(a.description.getOrElse("unknown"), a.term.getOrElse(True) /* TODO ake */, analysisSourceInfo, AssumptionType.Internal, enableCustomEdges_)
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
    val assumptionIds = assumptionLabels.filter(AssumptionAnalyzer.isAssumptionLabel).map(AssumptionAnalyzer.getIdFromLabel)
    val assertionIdsFromUnsatCore = assumptionLabels.filter(AssumptionAnalyzer.isAssertionLabel).map(AssumptionAnalyzer.getIdFromLabel)
    val assertionIdFromLabel = AssumptionAnalyzer.getIdFromLabel(assertionLabel)
    val assertionIds = assertionIdFromLabel +: assertionIdsFromUnsatCore // TODO ake: add check (not already contained)
    assumptionGraph.addEdges(assumptionIds, assertionIds)
    val axiomIds = assumptionLabels.filter(AssumptionAnalyzer.isAxiomLabel).map(AssumptionAnalyzer.getIdFromLabel)
    assumptionGraph.addEdges(axiomIds, assertionIds)
  }

  override def addPermissionInhaleNode(chunk: Chunk, permAmount: Option[ast.Exp], sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Option[Int] = {
    val node = PermissionInhaleNode(chunk, permAmount, True /* TODO ake */, sourceInfo, assumptionType, enableCustomEdges_)
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

  override def getNodeIds(terms: Set[Term]): Set[Int] = {
    assumptionGraph.nodes
      .filter(t => t.isInstanceOf[GeneralAssumptionNode] && terms.contains(t.asInstanceOf[GeneralAssumptionNode].getTerm))
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

  override def createLabelledConditionalChunks(decider: Decider, sourceChunks: Iterable[Chunk], thenTerm: Term, elseTerm: Term): Term = {
    val sourceNodeIds = getChunkNodeIds(sourceChunks.toSet)
    val labelNode = createAndAssumeLabelNode(decider, sourceNodeIds)
    Ite(labelNode.term, thenTerm, elseTerm)
  }

  override def createLabelledConditionalChunks(decider: Decider, sourceChunks: Iterable[Chunk], thenTerm: Term): Term = {
    val sourceNodeIds = getChunkNodeIds(sourceChunks.toSet)
    val labelNode = createAndAssumeLabelNode(decider, sourceNodeIds)
    Implies(labelNode.term, thenTerm)
  }

  private def createLabelNode(decider: Decider, sourceNodeIds: Iterable[Int]): LabelNode = {
    val (label, _) = decider.fresh(ast.LocalVar("analysisLabel", ast.Bool)())
    val labelNode = LabelNode(label)
    addNode(labelNode)
    assumptionGraph.addEdges(sourceNodeIds, labelNode.id)
    originalLabelNodes = originalLabelNodes :+ labelNode
    labelNode
  }

  override def createAndAssumeLabelNode(decider: Decider, sourceNodeIds: Iterable[Int]): LabelNode = {
    val labelNode = createLabelNode(decider, sourceNodeIds)
    val smtLabel = AssumptionAnalyzer.createAssumptionLabel(Some(labelNode.id))
    decider.assumeLabel(labelNode.term, smtLabel)
    labelNode
  }

  override def createLabelledConditional(decider: Decider, sourceTerms: Iterable[Term], term: Term): Term = {
    if(term.equals(True)) return term
    val sourceNodeIds = getNodeIds(sourceTerms.toSet) // TODO ake: maybe we have node id as argument
    if(sourceNodeIds.isEmpty) {
      term
    } else {
      val labelNode = createAndAssumeLabelNode(decider, sourceNodeIds)
      Implies(labelNode.term, term)
    }
  }

  override def createLabelledConditional(decider: Decider, sourceNodeId: Int, term: Term): Term = {
    val labelNode = createAndAssumeLabelNode(decider, Set(sourceNodeId))
    Implies(labelNode.term, term)
  }

  override def createLabelledConditional(decider: Decider, sourceTerms: Iterable[Term], terms: Seq[Term]): Seq[Term] = {
    if(!(terms exists (t => !t.equals(True)))) return terms
    val sourceNodeIds = getNodeIds(sourceTerms.toSet) // TODO ake: maybe we have node id as argument
    if(sourceNodeIds.isEmpty) {
      terms
    } else {
      val labelNode = createAndAssumeLabelNode(decider, sourceNodeIds)
      terms map (t => Implies(labelNode.term, t))
    }
  }

  private def reassumeLabel(decider: Decider, oldLabelNode: LabelNode): Unit = {
    val newLabelNode = LabelNode(oldLabelNode.term)
    // do not add to originalLabelNodes!
    addNode(newLabelNode)
    assumptionGraph.addEdges(Set(oldLabelNode.id), newLabelNode.id)
    val smtLabel = AssumptionAnalyzer.createAssumptionLabel(Some(newLabelNode.id))
    decider.assumeLabel(oldLabelNode.term, smtLabel)
  }

  override def reassumeLabels(decider: Decider): Unit = { // TODO ake: work with scopes!
    originalLabelNodes foreach (reassumeLabel(decider, _)) // assumes label
  }

  override def wrapWithLabel(labelNode: LabelNode, term: Term): Term = {
    Implies(labelNode.term, term)
  }

  override def wrapPermissionWithLabel(labelNode: LabelNode, term: Term): Term = {
    Ite(labelNode.term, term, NoPerm)
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
  override def getNodeIds(terms: Set[Term]): Set[Int] = Set.empty

  override def addDependencyFromExhaleToInhale(newChunkNodeId: Option[Int]): Unit = {}
  override def addPermissionDependencies(oldChunks: Set[Chunk], newChunkNode: Option[Int]): Unit = {
  }

  override def addPermissionDependencies(oldChunks: Set[Chunk], newChunkNodeId: Chunk): Unit = {}

  override def getMember: Option[ast.Member] = None

  override def addSingleAssumption(assumption: DebugExp, analysisSourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Option[Int] = None

  override def addAssumption(assumption: ast.Exp, term: Term, analysisSourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Option[Int] = None

  override def addAssumption(assumption: String, term: Term, analysisSourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Option[Int] = None
  override def exportGraph(): Unit = {}
}