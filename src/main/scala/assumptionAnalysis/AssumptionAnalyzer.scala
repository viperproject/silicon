package viper.silicon.assumptionAnalysis

import viper.silicon.assumptionAnalysis.AssumptionType.AssumptionType
import viper.silicon.debugger.DebugExp
import viper.silicon.interfaces.state.Chunk
import viper.silicon.state.terms.Term
import viper.silver.ast
import viper.silver.ast.{Member, NoPosition}


trait AssumptionAnalyzer {
  //  def pushScope(stmt: ast.Stmt): Unit
  //  def closeScope(): Unit
  def addPermissionNode(chunk: Chunk, sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Option[Int]

  def addSingleAssumption(assumption: ast.Exp, sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Option[Int]

  def addSingleAssumption(description: String, sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Option[Int]

  def addSingleAssumption(assumption: DebugExp, assumptionType: AssumptionType = AssumptionType.Unknown): Option[Int]

  def addSingleAssumption(assumption: DebugExp, sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Option[Int]

  def addAssumptions(assumptions: Iterable[DebugExp], sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Seq[Int]

  def addAssertion(assertion: Term, isAsserted: Boolean, sourceInfo: AnalysisSourceInfo): Option[Int]

  def addPermissionDependencies(oldChunks: Set[Chunk], newChunkNode: AssumptionAnalysisNode): Unit

  def processUnsatCoreAndAddDependencies(dep: String): Unit

  val assumptionGraph: AssumptionAnalysisGraph = new DefaultAssumptionAnalysisGraph()

  def getMethod: Option[ast.Method]
}

object AssumptionAnalyzer {
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

  override def addSingleAssumption(assumption: ast.Exp, sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Option[Int] = {
    val node = SimpleAssumptionNode(assumption, sourceInfo, assumptionType)
    addNode(node)
    Some(node.id)
  }

  override def addSingleAssumption(description: String, sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Option[Int] = {
    val node = StringAssumptionNode(description, sourceInfo, assumptionType)
    addNode(node)
    Some(node.id)
  }

  override def addSingleAssumption(assumption: DebugExp, assumptionType: AssumptionType = AssumptionType.Unknown): Option[Int] = {
    if(assumption.originalExp.isDefined) addSingleAssumption(assumption, ExpAnalysisSourceInfo(assumption.originalExp.get), assumptionType)
    else addSingleAssumption(assumption, StringAnalysisSourceInfo(assumption.description.getOrElse("unknown"), NoPosition), assumptionType)
  }

  override def addSingleAssumption(assumption: DebugExp, sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Option[Int] = {
    val node = if(assumption.originalExp.isDefined) SimpleAssumptionNode(assumption.originalExp.get, sourceInfo, assumptionType)
    else StringAssumptionNode(assumption.description.getOrElse("unknown"), sourceInfo, assumptionType)
    addNode(node)
    Some(node.id)
  }

  override def addAssumptions(assumptions: Iterable[DebugExp], sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Seq[Int] = {
    val newNodes = assumptions.filter(_.originalExp.isDefined)
      .map(a => SimpleAssumptionNode(a.originalExp.get, sourceInfo, assumptionType))
    newNodes foreach addNode
    newNodes.map(_.id).toSeq
  }

  override def addAssertion(assertion: Term, isAsserted: Boolean, sourceInfo: AnalysisSourceInfo): Option[Int] = {
    val newNode = SimpleAssertionNode(assertion, isAsserted, sourceInfo)
    addNode(newNode)
    Some(newNode.id)
  }

  override def processUnsatCoreAndAddDependencies(dep: String): Unit = {
    val assumptionLabels = dep.replace("(", "").replace(")", "").split(" ")
    if(assumptionLabels.size < 2) return
    val assumptionIds = assumptionLabels.filter(AssumptionAnalyzer.isAssumptionLabel).map(AssumptionAnalyzer.getIdFromLabel)
    val assertionIds = assumptionLabels.filter(AssumptionAnalyzer.isAssertionLabel).map(AssumptionAnalyzer.getIdFromLabel)
    assumptionGraph.addEdges(assumptionIds, assertionIds)
  }

  override def addPermissionNode(chunk: Chunk, sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Option[Int] = {
    val node = PermissionInhaleNode(chunk, sourceInfo, assumptionType)
    addNode(node)
    Some(node.id)
  }

  override def addPermissionDependencies(oldChunks: Set[Chunk], newChunkNode: AssumptionAnalysisNode): Unit = {
    val analysisChunks = assumptionGraph.nodes
      .filter(c => c.isInstanceOf[ChunkAnalysisInfo] && oldChunks.contains(c.asInstanceOf[ChunkAnalysisInfo].getChunk))
      .map(_.id).toSet
    addNode(newChunkNode)
    assumptionGraph.addEdges(analysisChunks, newChunkNode.id)
  }

  override def getMethod: Option[ast.Method] = Some(method)

}

class NoAssumptionAnalyzer extends AssumptionAnalyzer {

  override def addAssumptions(assumptions: Iterable[DebugExp], sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Seq[Int] = Seq.empty

  override def addAssertion(assertion: Term, isAsserted: Boolean, sourceInfo: AnalysisSourceInfo): Option[Int] = None

  override def processUnsatCoreAndAddDependencies(dep: String): Unit = {
  }

  override def addPermissionNode(chunk: Chunk, sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Option[Int] = None

  override def addPermissionDependencies(oldChunks: Set[Chunk], newChunkNode: AssumptionAnalysisNode): Unit = {
  }

  override def getMethod: Option[ast.Method] = None

  override def addSingleAssumption(assumption: DebugExp, assumptionType: AssumptionType = AssumptionType.Unknown): Option[Int] = None
  override def addSingleAssumption(assumption: DebugExp, sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Option[Int] = None
  override def addSingleAssumption(assumption: ast.Exp, sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Option[Int] = None
  override def addSingleAssumption(description: String, sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): Option[Int] = None
}