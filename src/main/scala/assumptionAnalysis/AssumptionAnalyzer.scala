package viper.silicon.assumptionAnalysis

import viper.silicon.assumptionAnalysis.AssumptionType.AssumptionType
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.debugger.DebugExp
import viper.silicon.interfaces.state.Chunk
import viper.silicon.state.terms.Term
import viper.silver.ast
import viper.silver.ast.{Exp, Member, NoPosition}


trait AssumptionAnalyzer {
  //  def pushScope(stmt: ast.Stmt): Unit
  //  def closeScope(): Unit
  def addPermissionInhaleNode(chunk: Chunk, permAmount: Option[ast.Exp], sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Option[Int]
  def addPermissionAssertNode(chunk: Chunk, permAmount: Option[ast.Exp], sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType = AssumptionType.Assertion): Option[Int]
  def addPermissionExhaleNode(chunk: Chunk, permAmount: Option[ast.Exp], sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType = AssumptionType.Assertion): Option[Int]
  def addPermissionNode(chunk: Chunk, permAmount: Option[ast.Exp], sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType = AssumptionType.Assertion, isExhale: Boolean=false): Option[Int]

  def addSingleAssumption(assumption: ast.Exp, analysisInfo: AnalysisInfo): Option[Int]

  def addSingleAssumption(description: String, analysisInfo: AnalysisInfo): Option[Int]

  def addSingleAssumption(assumption: DebugExp, assumptionType: AssumptionType = AssumptionType.Unknown): Option[Int]

  def addSingleAssumption(assumption: DebugExp, analysisInfo: AnalysisInfo): Option[Int]

  def addAssumptions(assumptions: Iterable[DebugExp], analysisInfo: AnalysisInfo): Seq[Int]

  def createAssertOrCheckNode(term: Term, assertion: Either[String, ast.Exp], analysisInfo: AnalysisInfo, isCheck: Boolean): Option[GeneralAssertionNode]

  def addPermissionDependencies(oldChunks: Set[Chunk], newChunkNodeId: Option[Int]): Unit

  def processUnsatCoreAndAddDependencies(dep: String): Unit

  val assumptionGraph: AssumptionAnalysisGraph = new DefaultAssumptionAnalysisGraph()

  var currentAnalysisInfo: AnalysisInfo = new NoAnalysisInfo()
  var currentExpStack: InsertionOrderedSet[ast.Exp] = InsertionOrderedSet.empty

  def setCurrentAnalysisInfo(analysisSourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): AnalysisInfo = {
    currentAnalysisInfo = AnalysisInfo(this, analysisSourceInfo, assumptionType)
    currentAnalysisInfo
  }

  def clearCurrentAnalysisInfo(): AnalysisInfo = {
    currentAnalysisInfo = new NoAnalysisInfo()
    currentAnalysisInfo
  }

  def updateCurrentAnalysisInfo(at: AssumptionType): AnalysisInfo = {
    setCurrentAnalysisInfo(currentAnalysisInfo.sourceInfo, at)
  }

  def updateCurrentAnalysisInfo(si: AnalysisSourceInfo): AnalysisInfo = {
    setCurrentAnalysisInfo(si, currentAnalysisInfo.assumptionType)
  }

  def updateCurrentAnalysisInfo(si: AnalysisSourceInfo, at: AssumptionType): AnalysisInfo = {
    setCurrentAnalysisInfo(si, at)
  }

  def getMember: Option[Member]
}

object AssumptionAnalyzer {
  val noAssumptionAnalyzerSingelton = new NoAssumptionAnalyzer()

  def createAssumptionLabel(id: Option[Int], offset: Int = 0): String = {
    createLabel("assumption", id, offset)
  }

  def createAssertionLabel(id: Option[Int], offset: Int = 0): String = {
    createLabel("assertion", id, offset)
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
}

class DefaultAssumptionAnalyzer(member: Member) extends AssumptionAnalyzer {
  //  private var scope : mutable.Set[AssumptionAnalysisNode] = mutable.Set.empty
  //  private var isScopeOpen: Boolean = false
  //  private var scopeStmt: ast.Stmt = ???


  //  override def pushScope(stmt: ast.Stmt): Unit = {
  ////    scopeStmt = stmt
  //    scope = mutable.Set.empty
  //    isScopeOpen = true
  //  }
  //
  //  override def closeScope(): Unit = {
  ////    assumptionGraph.addNode(new StatementGroupNode(scopeStmt, scope.toSet))
  //    scope = mutable.Set.empty
  //    isScopeOpen = false
  //  }

  def addNode(node: AssumptionAnalysisNode): Unit = {
    assumptionGraph.addNode(node)
  }

  override def addSingleAssumption(assumption: ast.Exp, analysisInfo: AnalysisInfo): Option[Int] = {
    val node = SimpleAssumptionNode(assumption, analysisInfo.sourceInfo, analysisInfo.assumptionType)
    addNode(node)
    Some(node.id)
  }

  override def addSingleAssumption(description: String, analysisInfo: AnalysisInfo): Option[Int] = {
    val node = StringAssumptionNode(description, analysisInfo.sourceInfo, analysisInfo.assumptionType)
    addNode(node)
    Some(node.id)
  }

  override def addSingleAssumption(assumption: DebugExp, assumptionType: AssumptionType = AssumptionType.Unknown): Option[Int] = {
    if(assumption.originalExp.isDefined) addSingleAssumption(assumption, AnalysisInfo(this, ExpAnalysisSourceInfo(assumption.originalExp.get), assumptionType))
    else addSingleAssumption(assumption, AnalysisInfo(this, StringAnalysisSourceInfo(assumption.description.getOrElse("unknown"), NoPosition), assumptionType))
  }

  override def addSingleAssumption(assumption: DebugExp, analysisInfo: AnalysisInfo): Option[Int] = {
    val node = if(assumption.originalExp.isDefined) SimpleAssumptionNode(assumption.originalExp.get, analysisInfo.sourceInfo, analysisInfo.assumptionType)
    else StringAssumptionNode(assumption.description.getOrElse("unknown"), analysisInfo.sourceInfo, analysisInfo.assumptionType)
    addNode(node)
    Some(node.id)
  }

  override def addAssumptions(assumptions: Iterable[DebugExp], analysisInfo: AnalysisInfo): Seq[Int] = {
    val newNodes = assumptions.filter(_.originalExp.isDefined)
      .map(a => SimpleAssumptionNode(a.originalExp.get, analysisInfo.sourceInfo, analysisInfo.assumptionType))
    newNodes foreach addNode
    newNodes.map(_.id).toSeq
  }

  override def createAssertOrCheckNode(term: Term, assertion: Either[String, ast.Exp], analysisInfo: AnalysisInfo, isCheck: Boolean): Option[GeneralAssertionNode] = {
    if(isCheck) return Some(SimpleCheckNode(term, analysisInfo.sourceInfo, analysisInfo.assumptionType))

    Some(assertion match {
      case Left(description) => StringAssertionNode(description, analysisInfo.sourceInfo, analysisInfo.assumptionType)
      case Right(exp) => SimpleAssertionNode(exp, analysisInfo.sourceInfo, analysisInfo.assumptionType)
    })
  }

  override def processUnsatCoreAndAddDependencies(dep: String): Unit = {
    val assumptionLabels = dep.replace("(", "").replace(")", "").split(" ")
    if(assumptionLabels.size < 2) return
    val assumptionIds = assumptionLabels.filter(AssumptionAnalyzer.isAssumptionLabel).map(AssumptionAnalyzer.getIdFromLabel)
    val assertionIds = assumptionLabels.filter(AssumptionAnalyzer.isAssertionLabel).map(AssumptionAnalyzer.getIdFromLabel)
    assumptionGraph.addEdges(assumptionIds, assertionIds)
  }

  override def addPermissionInhaleNode(chunk: Chunk, permAmount: Option[ast.Exp], sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Option[Int] = {
    val node = PermissionInhaleNode(chunk, permAmount, sourceInfo, assumptionType)
    addNode(node)
    Some(node.id)
  }

  override def addPermissionAssertNode(chunk: Chunk, permAmount: Option[ast.Exp], sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType = AssumptionType.Assertion): Option[Int] = {
    val node = PermissionAssertNode(chunk, permAmount, sourceInfo, assumptionType)
    addNode(node)
    addPermissionDependencies(Set(chunk), Some(node.id))
    Some(node.id)
  }

  override def addPermissionExhaleNode(chunk: Chunk, permAmount: Option[ast.Exp], sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType = AssumptionType.Assertion): Option[Int] = {
    val node = PermissionExhaleNode(chunk, permAmount, sourceInfo, assumptionType)
    addNode(node)
    addPermissionDependencies(Set(chunk), Some(node.id))
    Some(node.id)
  }

  override def addPermissionNode(chunk: Chunk, permAmount: Option[Exp], sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType, isExhale: Boolean=false): Option[Int] = {
    val nodeFunction = if(isExhale) addPermissionExhaleNode _ else addPermissionInhaleNode _
    nodeFunction(chunk, permAmount, sourceInfo, assumptionType)
  }

  override def addPermissionDependencies(oldChunks: Set[Chunk], newChunkNodeId: Option[Int]): Unit = {
    if(newChunkNodeId.isEmpty) return

    val oldChunkNodeIds = assumptionGraph.nodes
      .filter(c => c.id != newChunkNodeId.get && !c.isInstanceOf[PermissionAssertNode] && c.isInstanceOf[ChunkAnalysisInfo] && oldChunks.contains(c.asInstanceOf[ChunkAnalysisInfo].getChunk))
      .map(_.id).toSet
    assumptionGraph.addEdges(oldChunkNodeIds, newChunkNodeId.get)
  }

  override def getMember: Option[Member] = Some(member)

}

class NoAssumptionAnalyzer extends AssumptionAnalyzer {

  override def addAssumptions(assumptions: Iterable[DebugExp], analysisInfo: AnalysisInfo): Seq[Int] = Seq.empty

  override def createAssertOrCheckNode(term: Term, assertion: Either[String, ast.Exp], analysisInfo: AnalysisInfo, isCheck: Boolean): Option[GeneralAssertionNode] = None

  override def processUnsatCoreAndAddDependencies(dep: String): Unit = {
  }

  override def addPermissionInhaleNode(chunk: Chunk, permAmount: Option[ast.Exp], sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Option[Int] = None
  override def addPermissionExhaleNode(chunk: Chunk, permAmount: Option[ast.Exp], sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Option[Int] = None
  override def addPermissionAssertNode(chunk: Chunk, permAmount: Option[ast.Exp], sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Option[Int] = None
  override def addPermissionNode(chunk: Chunk, permAmount: Option[ast.Exp], sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType, isExhale: Boolean=false): Option[Int] = None

  override def addPermissionDependencies(oldChunks: Set[Chunk], newChunkNode: Option[Int]): Unit = {
  }

  override def getMember: Option[Member] = None

  override def addSingleAssumption(assumption: DebugExp, assumptionType: AssumptionType = AssumptionType.Unknown): Option[Int] = None
  override def addSingleAssumption(assumption: DebugExp, analysisInfo: AnalysisInfo): Option[Int] = None
  override def addSingleAssumption(assumption: ast.Exp, analysisInfo: AnalysisInfo): Option[Int] = None
  override def addSingleAssumption(description: String, analysisInfo: AnalysisInfo): Option[Int] = None
}