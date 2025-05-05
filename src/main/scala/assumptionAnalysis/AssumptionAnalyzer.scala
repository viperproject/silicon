package viper.silicon.assumptionAnalysis

import viper.silicon.debugger.DebugExp
import viper.silicon.interfaces.state.Chunk
import viper.silicon.state.BasicChunk
import viper.silicon.state.terms.Term
import viper.silver.ast
import viper.silver.ast.Stmt

import scala.collection.mutable


trait AssumptionAnalyzer {
  def pushScope(stmt: ast.Stmt): Unit
  def closeScope(): Unit
  def addAssumptionNode(assumption: AssumptionAnalysisNode): Unit
  def addAssumptions(assumptions: Iterable[DebugExp]): Unit
  def addAssertion(assertion: Term): Unit
  def addChunkNode(oldChunks: Set[Chunk], newChunkNode: AssumptionAnalysisNode)
  def addDependency(dep: String): Unit

  val assumptionGraph: AssumptionAnalysisGraph = new DefaultAssumptionAnalysisGraph()
}

class DefaultAssumptionAnalyzer extends AssumptionAnalyzer {
  private var scope : mutable.Set[AssumptionAnalysisNode] = mutable.Set.empty
  private var isScopeOpen: Boolean = false
  private var scopeStmt: ast.Stmt = ast.Goto("nop")()

  override def pushScope(stmt: ast.Stmt): Unit = {
    scopeStmt = stmt
    scope = mutable.Set.empty
    isScopeOpen = true
  }

  override def closeScope(): Unit = {
//    assumptionGraph.addNode(new StatementGroupNode(scopeStmt, scope.toSet))
    scope = mutable.Set.empty
    isScopeOpen = false
  }

  override def addAssumptions(assumptions: Iterable[DebugExp]): Unit = {
    val newNodes = assumptions.filter(_.originalExp.isDefined)
      .map(a => new SimpleAssumptionNode(a.originalExp.get))
    assumptionGraph.addNodes(newNodes.toSet)
    if(isScopeOpen) scope.addAll(newNodes)
  }

  override def addAssertion(assertion: Term): Unit = {
    val newNode = new SimpleAssertionNode(assertion)
    assumptionGraph.addNode(newNode)
    if(isScopeOpen) scope.addOne(newNode)
  }

  override def addDependency(dep: String): Unit = {
    val assumptions = dep.split(" ")
  }

  override def addAssumptionNode(assumption: AssumptionAnalysisNode): Unit = {
    assumptionGraph.addNode(assumption)
  }

  override def addChunkNode(oldChunks: Set[Chunk], newChunkNode: AssumptionAnalysisNode): Unit = {
    val analysisChunks = assumptionGraph.nodes.values
      .filter(c => c.isInstanceOf[ChunkAnalysisInfo] && oldChunks.contains(c.asInstanceOf[ChunkAnalysisInfo].getChunk))
      .map(_.id).toSet
    addAssumptionNode(newChunkNode)
    assumptionGraph.addEdges(analysisChunks, newChunkNode.id)
  }
}

class NoAssumptionAnalyzer extends AssumptionAnalyzer {

  override def pushScope(stmt: Stmt): Unit = {
  }

  override def closeScope(): Unit = {
  }

  override def addAssumptions(assumptions: Iterable[DebugExp]): Unit = {
  }

  override def addAssertion(assertion: Term): Unit = {
  }

  override def addDependency(dep: String): Unit = {
  }

  override def addAssumptionNode(assumption: AssumptionAnalysisNode): Unit = {
  }

  override def addChunkNode(oldChunks: Set[Chunk], newChunkNode: AssumptionAnalysisNode): Unit = {
  }
}