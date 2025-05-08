package viper.silicon.assumptionAnalysis

import viper.silicon.debugger.DebugExp
import viper.silicon.interfaces.state.Chunk
import viper.silicon.state.terms.Term
import viper.silver.ast


trait AssumptionAnalyzer {
//  def pushScope(stmt: ast.Stmt): Unit
//  def closeScope(): Unit
  def addAssumptionNode(assumption: AssumptionAnalysisNode): Unit
  def addSingleAssumption(assumption: DebugExp): Option[Int]
  def addAssumptions(assumptions: Iterable[DebugExp]): Seq[Int]
  def addAssertion(assertion: Term): Option[Int]
  def addChunkNode(oldChunks: Set[Chunk], newChunkNode: AssumptionAnalysisNode)
  def addDependency(dep: String): Unit

  val assumptionGraph: AssumptionAnalysisGraph = new DefaultAssumptionAnalysisGraph()

  def getMethod: Option[ast.Method]

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
    val node = if(assumption.originalExp.isDefined) new SimpleAssumptionNode(assumption.originalExp.get)
    else new StringAssumptionNode(assumption.description.getOrElse("unknown"))
    assumptionGraph.addNode(node)
    Some(node.id)
  }

  override def addAssumptions(assumptions: Iterable[DebugExp]): Seq[Int] = {
    val newNodes = assumptions.filter(_.originalExp.isDefined)
      .map(a => new SimpleAssumptionNode(a.originalExp.get))
    assumptionGraph.addNodes(newNodes.toSet)
    newNodes.map(_.id).toSeq
  }

  override def addAssertion(assertion: Term): Option[Int] = {
    val newNode = new SimpleAssertionNode(assertion)
    assumptionGraph.addNode(newNode)
    Some(newNode.id)
  }

  override def addDependency(dep: String): Unit = {
    val assumptionLabels = dep.replace("(", "").replace(")", "").split(" ")
    if(assumptionLabels.size < 2) return
    val ids: Iterable[Int] = assumptionLabels map (l => l.split("_").tail.head.toInt)
    val maxId: Int = ids.reduce[Int]{case (a, b) => math.max(a, b)}
    assumptionGraph.addEdges(ids.filter(_ != maxId), maxId)
  }

  override def addAssumptionNode(assumption: AssumptionAnalysisNode): Unit = {
    assumptionGraph.addNode(assumption)
  }

  override def addChunkNode(oldChunks: Set[Chunk], newChunkNode: AssumptionAnalysisNode): Unit = {
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

  override def addAssertion(assertion: Term): Option[Int] = {
    None
  }

  override def addDependency(dep: String): Unit = {
  }

  override def addAssumptionNode(assumption: AssumptionAnalysisNode): Unit = {
  }

  override def addChunkNode(oldChunks: Set[Chunk], newChunkNode: AssumptionAnalysisNode): Unit = {
  }

  override def getMethod: Option[ast.Method] = None

  override def addSingleAssumption(assumption: DebugExp): Option[Int] = {
    None
  }
}