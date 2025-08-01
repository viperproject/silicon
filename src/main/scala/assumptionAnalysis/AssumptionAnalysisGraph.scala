package viper.silicon.assumptionAnalysis

import java.io.{File, PrintWriter}
import java.util.concurrent.atomic.AtomicInteger
import scala.collection.mutable


object AssumptionAnalysisGraphHelper {
  private val idCounter: AtomicInteger = new AtomicInteger(0)

  def nextId(): Int = {
    idCounter.getAndIncrement()
  }
}

trait ReadOnlyAssumptionAnalysisGraph {
  def getNodes: Seq[AssumptionAnalysisNode]
  def getDirectEdges: Map[Int, Set[Int]] // target -> direct dependencies
  def getTransitiveEdges: Map[Int, Set[Int]] // target -> direct dependencies
  def getAllEdges: Map[Int, Set[Int]] // target -> direct dependencies

  def existsAnyDependency(sources: Set[Int], targets: Set[Int], includeInfeasibilityNodes: Boolean): Boolean
  def getAllDependencies(sources: Set[Int], includeInfeasibilityNodes: Boolean): Set[Int]
  def getAllDependents(sources: Set[Int], includeInfeasibilityNodes: Boolean): Set[Int]

  def exportGraph(dirName: String): Unit
}

class AssumptionAnalysisGraph extends ReadOnlyAssumptionAnalysisGraph {
  var nodes: mutable.Seq[AssumptionAnalysisNode] = mutable.Seq()
  private val edges: mutable.Map[Int, Set[Int]] = mutable.Map.empty
  private val transitiveEdges: mutable.Map[Int, Set[Int]] = mutable.Map.empty

  def getNodes: Seq[AssumptionAnalysisNode] = nodes.toSeq
  def getDirectEdges: Map[Int, Set[Int]] = edges.toMap
  def getTransitiveEdges: Map[Int, Set[Int]] = transitiveEdges.toMap
  def getAllEdges: Map[Int, Set[Int]] = {
    val keys = edges.keySet ++ transitiveEdges.keySet
    val res = mutable.Map[Int, Set[Int]]()
    keys foreach {key =>
      res.update(key, edges.getOrElse(key, Set()) ++ transitiveEdges.getOrElse(key, Set()))
    }
    res.toMap
  }

  def addNode(node: AssumptionAnalysisNode): Unit = {
    nodes = nodes :+ node
  }

  def addNodes(nodes: Iterable[AssumptionAnalysisNode]): Unit = {
    nodes foreach addNode
  }

  def addEdges(source: Int, targets: Iterable[Int]): Unit = {
    addEdges(Set(source), targets)
  }

  def addEdges(sources: Iterable[Int], target: Int): Unit = {
    val oldSources = edges.getOrElse(target, Set.empty)
    val newSources = sources.filter(_ != target)
    if(newSources.nonEmpty)
      edges.update(target, oldSources ++ newSources)
  }

  def addEdges(sources: Iterable[Int], targets: Iterable[Int]): Unit = {
    targets foreach (addEdges(sources, _))
  }

  def existsAnyDependency(sources: Set[Int], targets: Set[Int], includeInfeasibilityNodes: Boolean): Boolean = {
    val infeasibilityNodeIds: Set[Int] = if(includeInfeasibilityNodes) Set.empty else (getNodes filter (_.isInstanceOf[InfeasibilityNode]) map (_.id)).toSet
    var visited: Set[Int] = Set.empty
    var queue: List[Int] = targets.toList
    val allEdges = getAllEdges
    while(queue.nonEmpty){
      val curr = queue.head
      val newVisits = allEdges.getOrElse(curr, Set()).diff(infeasibilityNodeIds)
      if(newVisits.intersect(sources).nonEmpty)
        return true
      visited = visited ++ Set(curr)
      queue = queue.tail ++ (newVisits filter (!visited.contains(_)))
    }
    false
  }

  def getAllDependencies(targets: Set[Int], includeInfeasibilityNodes: Boolean): Set[Int] = {
    val infeasibilityNodeIds: Set[Int] = if(includeInfeasibilityNodes) Set.empty else (getNodes filter (_.isInstanceOf[InfeasibilityNode]) map (_.id)).toSet
    var visited: Set[Int] = Set.empty
    var queue: List[Int] = targets.toList
    val allEdges = getAllEdges
    while(queue.nonEmpty){
      val curr = queue.head
      val newVisits = allEdges.getOrElse(curr, Set()).diff(infeasibilityNodeIds)
      visited = visited ++ Set(curr)
      queue = queue.tail ++ (newVisits filter (!visited.contains(_)))
    }
    visited
  }

  def getAllDependents(sources: Set[Int], includeInfeasibilityNodes: Boolean): Set[Int] = {
    val infeasibilityNodeIds: Set[Int] = if(includeInfeasibilityNodes) Set.empty else (getNodes filter (_.isInstanceOf[InfeasibilityNode]) map (_.id)).toSet
    var visited: Set[Int] = Set.empty
    var queue: Set[Int] = sources
    val allEdges = getAllEdges
    while(queue.nonEmpty){
      val newVisits = allEdges.filter{case (t, s) => s.intersect(queue).nonEmpty && !infeasibilityNodeIds.contains(t)}.keys.toSet
      visited = visited ++ queue
      queue = newVisits diff visited
    }
    visited
  }

  private def addTransitiveEdges(sources: Iterable[AssumptionAnalysisNode], target: AssumptionAnalysisNode): Unit = {
    val oldSources = transitiveEdges.getOrElse(target.id, Set.empty)
    val newSources = sources map(_.id) // filter(_ > target.id) does not work due to loop invariants
    if(newSources.nonEmpty) transitiveEdges.update(target.id, oldSources ++ newSources)
  }

  private def addTransitiveEdges(sources: Iterable[AssumptionAnalysisNode], targets: Iterable[AssumptionAnalysisNode]): Unit = {
    targets foreach (t => addTransitiveEdges(sources, t))
  }

  // TODO ake: maybe move to AssumptionAnalyzer?
  private def getNodesPerTransitivitySourceInfo: Map[String, Seq[AssumptionAnalysisNode]] = {
    getNodes.groupBy(_.sourceInfo.getSourceForTransitiveEdges.toString)
  }

  // TODO ake: maybe move to AssumptionAnalyzer?
  def addTransitiveEdges(): Unit = {
    val nodesPerSourceInfo = getNodesPerTransitivitySourceInfo
    nodesPerSourceInfo foreach {nodes =>
      val asserts = nodes._2.filter(_.isInstanceOf[GeneralAssertionNode])
      val assumes = nodes._2.filter(n => !n.isClosed && n.isInstanceOf[GeneralAssumptionNode] && !n.isInstanceOf[LabelNode])
      addTransitiveEdges(asserts, assumes)
      val checks = asserts.filter(_.isInstanceOf[SimpleCheckNode])
      val notChecks = nodes._2.filter(n => !n.isClosed && !n.isInstanceOf[SimpleCheckNode])
      addTransitiveEdges(checks, notChecks)
    }
  }

  private def removeAllEdgesForNode(node: AssumptionAnalysisNode): Unit = {
    val id = node.id
    val predecessors = (edges filter { case (_, t) => t.contains(id) }).keys
    val successors = edges.getOrElse(id, Set.empty)
    edges.remove(id)
    predecessors foreach (pid => edges.update(pid, edges.getOrElse(pid, Set.empty).filter(_ != id)))
    addEdges(successors, predecessors)
  }

  // TODO ake: maybe move to AssumptionAnalyzer?
  def removeLabelNodes(): Unit = {
    nodes filter (_.isInstanceOf[LabelNode]) foreach removeAllEdgesForNode
    nodes = nodes filter (!_.isInstanceOf[LabelNode])
  }

  def exportGraph(dirName: String): Unit = {
    val directory = new File(dirName)
    directory.mkdir()
    exportNodes(dirName + "/nodes.csv")
    exportEdges(dirName + "/edges.csv")
  }

  private def exportEdges(fileName: String): Unit = {
    val writer = new PrintWriter(fileName)
    writer.println("source,target,label")
    edges foreach (e => e._2 foreach (t => writer.println(e._1.toString + "," + t + ",direct")))
    transitiveEdges foreach (e => e._2 foreach (t => writer.println(e._1.toString + "," + t + ",transitive")))
    writer.close()
  }

  private def exportNodes(fileName: String): Unit = {
    val sep = "#"
    def getNodeExportString(node: AssumptionAnalysisNode): String = {
      val parts = mutable.Seq(node.id.toString, node.getNodeType, node.assumptionType.toString, node.getNodeString, node.sourceInfo.toString, node.sourceInfo.getPositionString, node.sourceInfo.getFineGrainedSource.toString)
      parts.map(_.replace("#", "@")).mkString(sep)
    }
    val writer = new PrintWriter(fileName)
    val headerParts = mutable.Seq("id", "node type", "assumption type", "node info", "source info", "position", "fine grained source")
    writer.println(headerParts.mkString(sep))
    nodes foreach (n => writer.println(getNodeExportString(n).replace("\n", " ")))
    writer.close()
  }
}


