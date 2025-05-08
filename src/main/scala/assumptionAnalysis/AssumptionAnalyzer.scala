package viper.silicon.assumptionAnalysis

import viper.silicon.debugger.DebugExp
import viper.silicon.interfaces.state.Chunk
import viper.silicon.state.terms.Term
import viper.silver.ast
import viper.silver.ast.NoPosition


trait AssumptionAnalyzer {
//  def pushScope(stmt: ast.Stmt): Unit
//  def closeScope(): Unit
  def addAssumptionNode(assumption: AssumptionAnalysisNode): Unit
  def addSingleAssumption(assumption: DebugExp): Option[Int]
  def addAssumptions(assumptions: Iterable[DebugExp]): Seq[Int]
  def addAssertion(assertion: Term, isAsserted: Boolean, sourceInfo: AnalysisSourceInfo): Option[Int]
  def addPermissionDependencies(oldChunks: Set[Chunk], newChunkNode: AssumptionAnalysisNode): Unit
  def processUnsatCore(dep: String): Unit

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

class DefaultAssumptionAnalyzer(method: ast.Method) extends AssumptionAnalyzer {
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

  override def addSingleAssumption(assumption: DebugExp): Option[Int] = {
    val node = if(assumption.originalExp.isDefined) SimpleAssumptionNode(assumption.originalExp.get, ExpAnalysisSourceInfo(assumption.originalExp.get), AssumptionType.Unknown)
    else StringAssumptionNode(assumption.description.getOrElse("unknown"), StringAnalysisSourceInfo(assumption.description.getOrElse("unknown"), NoPosition), AssumptionType.Unknown)
    assumptionGraph.addNode(node)
    Some(node.id)
  }

  override def addAssumptions(assumptions: Iterable[DebugExp]): Seq[Int] = {
    val newNodes = assumptions.filter(_.originalExp.isDefined)
      .map(a => SimpleAssumptionNode(a.originalExp.get, ExpAnalysisSourceInfo(a.originalExp.get), AssumptionType.Unknown))
    assumptionGraph.addNodes(newNodes.toSet)
    newNodes.map(_.id).toSeq
  }

  override def addAssertion(assertion: Term, isAsserted: Boolean, sourceInfo: AnalysisSourceInfo): Option[Int] = {
    val newNode = SimpleAssertionNode(assertion, isAsserted, sourceInfo)
    assumptionGraph.addNode(newNode)
    Some(newNode.id)
  }

  override def processUnsatCore(dep: String): Unit = {
    val assumptionLabels = dep.replace("(", "").replace(")", "").split(" ")
    if(assumptionLabels.size < 2) return
    val assumptionIds = assumptionLabels.filter(AssumptionAnalyzer.isAssumptionLabel).map(AssumptionAnalyzer.getIdFromLabel)
    val assertionIds = assumptionLabels.filter(AssumptionAnalyzer.isAssertionLabel).map(AssumptionAnalyzer.getIdFromLabel)
    assumptionGraph.addEdges(assumptionIds, assertionIds)
  }

  override def addAssumptionNode(assumption: AssumptionAnalysisNode): Unit = {
    assumptionGraph.addNode(assumption)
  }

  override def addPermissionDependencies(oldChunks: Set[Chunk], newChunkNode: AssumptionAnalysisNode): Unit = {
    val analysisChunks = assumptionGraph.nodes
      .filter(c => c.isInstanceOf[ChunkAnalysisInfo] && oldChunks.contains(c.asInstanceOf[ChunkAnalysisInfo].getChunk))
      .map(_.id).toSet
    addAssumptionNode(newChunkNode)
    assumptionGraph.addEdges(analysisChunks, newChunkNode.id)
  }

  override def getMethod: Option[ast.Method] = Some(method)

}

class NoAssumptionAnalyzer extends AssumptionAnalyzer {

  override def addAssumptions(assumptions: Iterable[DebugExp]): Seq[Int] = {
    Seq.empty
  }

  override def addAssertion(assertion: Term, isAsserted: Boolean, sourceInfo: AnalysisSourceInfo): Option[Int] = {
    None
  }

  override def processUnsatCore(dep: String): Unit = {
  }

  override def addAssumptionNode(assumption: AssumptionAnalysisNode): Unit = {
  }

  override def addPermissionDependencies(oldChunks: Set[Chunk], newChunkNode: AssumptionAnalysisNode): Unit = {
  }

  override def getMethod: Option[ast.Method] = None

  override def addSingleAssumption(assumption: DebugExp): Option[Int] = {
    None
  }
}