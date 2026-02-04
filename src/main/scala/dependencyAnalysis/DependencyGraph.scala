package viper.silicon.dependencyAnalysis

import viper.silver.dependencyAnalysis.AbstractReadOnlyDependencyGraph

import java.io.PrintWriter
import java.nio.file.Paths
import java.util.concurrent.atomic.AtomicInteger
import scala.collection.mutable


object DependencyGraphHelper {
  private val idCounter: AtomicInteger = new AtomicInteger(0)

  def nextId(): Int = {
    idCounter.getAndIncrement()
  }
}

trait ReadOnlyDependencyGraph extends AbstractReadOnlyDependencyGraph {
  def getNodes: Seq[DependencyAnalysisNode]
  def getAssumptionNodes: Seq[GeneralAssumptionNode]
  def getAssertionNodes: Seq[GeneralAssertionNode]
  def getDirectEdges: Map[Int, Set[Int]] // target -> direct dependencies
  def getEdgesConnectingMethods: Map[Int, Set[Int]]
  def getAllEdges: Map[Int, Set[Int]] // target -> direct dependencies

  def existsAnyDependency(sources: Set[Int], targets: Set[Int], includeInfeasibilityNodes: Boolean): Boolean
  def getAllDependencies(sources: Set[Int], includeInfeasibilityNodes: Boolean, includeIntraMethodEdges: Boolean=true): Set[Int]
  def getAllDependents(sources: Set[Int], includeInfeasibilityNodes: Boolean): Set[Int]

  def exportGraph(dirName: String): Unit
}

class DependencyGraph extends ReadOnlyDependencyGraph {
  private var assumptionNodes: mutable.Seq[GeneralAssumptionNode] = mutable.Seq()
  private var assertionNodes: mutable.Seq[GeneralAssertionNode] = mutable.Seq()
  private val edges: mutable.Map[Int, Set[Int]] = mutable.Map.empty
  private val edgesConnectingMethods: mutable.Map[Int, Set[Int]] = mutable.Map.empty // keep this, it's relevant for computing verification progress

  def getNodes: Seq[DependencyAnalysisNode] = getAssumptionNodes ++ getAssertionNodes
  def getAssumptionNodes: Seq[GeneralAssumptionNode] = assumptionNodes.toSeq
  def getAssertionNodes: Seq[GeneralAssertionNode] = assertionNodes.toSeq
  def getDirectEdges: Map[Int, Set[Int]] = edges.toMap
  def getEdgesConnectingMethods: Map[Int, Set[Int]] = edgesConnectingMethods.toMap

  def getIntraMethodEdges: Map[Int, Set[Int]] = {
    val keys = edges.keySet
    val intraMethodEdges = mutable.Map[Int, Set[Int]]()
    keys foreach {key =>
      intraMethodEdges.update(key, edges.getOrElse(key, Set()))
    }
    intraMethodEdges.toMap
  }

  def getAllEdges: Map[Int, Set[Int]] = {
    val intraMethodEdges = getIntraMethodEdges
    val keys = intraMethodEdges.keySet ++ edgesConnectingMethods.keySet
    val allEdges = mutable.Map[Int, Set[Int]]()
    keys foreach {key =>
      allEdges.update(key, intraMethodEdges.getOrElse(key, Set()) ++ edgesConnectingMethods.getOrElse(key, Set()))
    }
    allEdges.toMap
  }

  // TODO ake: remove
  def setEdges(newEdges: Map[Int, Set[Int]]): Unit = {
    newEdges.foreach(e => edges.update(e._1, e._2))
  }

  def addAssumptionNode(node: GeneralAssumptionNode): Unit = {
    assumptionNodes = assumptionNodes :+ node
  }

  def addAssumptionNodes(newNodes: Iterable[GeneralAssumptionNode]): Unit = {
    assumptionNodes = assumptionNodes ++ newNodes
  }

  def addNode(node: DependencyAnalysisNode): Unit = {
    node match {
      case node: GeneralAssertionNode => addAssertionNode(node)
      case node: GeneralAssumptionNode => addAssumptionNode(node)
      case _ => assert(false)
    }
  }

  def addAssertionNode(node: GeneralAssertionNode): Unit = {
    assertionNodes = assertionNodes :+ node
  }

  def addAssertionNodes(newNodes: Iterable[GeneralAssertionNode]): Unit = {
    assertionNodes = assertionNodes ++ newNodes
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

  def addEdgesConnectingMethods(sources: Iterable[Int], target: Int): Unit = {
    val oldSources = edgesConnectingMethods.getOrElse(target, Set.empty)
    val newSources = sources.filter(_ != target)
    if(newSources.nonEmpty)
      edgesConnectingMethods.update(target, oldSources ++ newSources)
  }

  def addEdgesConnectingMethods(sources: Iterable[Int], targets: Iterable[Int]): Unit = {
    targets foreach (addEdgesConnectingMethods(sources, _))
  }

  def addEdgesConnectingMethods(source: Int, targets: Iterable[Int]): Unit = {
    addEdgesConnectingMethods(Set(source), targets)
  }

  def existsAnyDependency(sources: Set[Int], targets: Set[Int], includeInfeasibilityNodes: Boolean): Boolean = {
    val infeasibilityNodeIds: Set[Int] = if(includeInfeasibilityNodes) Set.empty else (getAssumptionNodes filter (_.isInstanceOf[InfeasibilityNode]) map (_.id)).toSet
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

  def getAllDependencies(targets: Set[Int], includeInfeasibilityNodes: Boolean, includeEdgesConnectingMethods: Boolean=true): Set[Int] = {
    val infeasibilityNodeIds: Set[Int] = if(includeInfeasibilityNodes) Set.empty else (getAssumptionNodes filter (_.isInstanceOf[InfeasibilityNode]) map (_.id)).toSet
    var visited: Set[Int] = Set.empty
    var queue: List[Int] = targets.toList
    val allEdges = if(includeEdgesConnectingMethods) getAllEdges else getIntraMethodEdges
    while(queue.nonEmpty){
      val curr = queue.head
      val newVisits = allEdges.getOrElse(curr, Set()).diff(infeasibilityNodeIds)
      visited = visited ++ Set(curr)
      queue = queue.tail ++ (newVisits filter (!visited.contains(_)))
    }
    visited
  }

  def getAllDependents(sources: Set[Int], includeInfeasibilityNodes: Boolean): Set[Int] = {
    val infeasibilityNodeIds: Set[Int] = if(includeInfeasibilityNodes) Set.empty else (getAssumptionNodes filter (_.isInstanceOf[InfeasibilityNode]) map (_.id)).toSet
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

  private def addTransitiveEdges(sources: Iterable[DependencyAnalysisNode], target: DependencyAnalysisNode): Unit = {
    val oldSources = edges.getOrElse(target.id, Set.empty)
    val newSources = sources map(_.id) // filter(_ > target.id) does not work due to loop invariants
    if(newSources.nonEmpty) edges.update(target.id, oldSources ++ newSources)
  }

  private def addTransitiveEdges(sources: Iterable[DependencyAnalysisNode], targets: Iterable[DependencyAnalysisNode]): Unit = {
    targets foreach (t => addTransitiveEdges(sources, t))
  }

  // TODO ake: maybe move to DependencyAnalyzer?
  private def getNodesPerTransitivitySourceInfo: Map[AnalysisSourceInfo, Seq[DependencyAnalysisNode]] = {
    getNodes.groupBy(_.sourceInfo.getSourceForTransitiveEdges)
  }

  // TODO ake: maybe move to DependencyAnalyzer?
  def addTransitiveEdges(): Unit = {
    val nodesPerSourceInfo = getNodesPerTransitivitySourceInfo
    nodesPerSourceInfo foreach {case (_, nodes) =>
      val asserts = nodes.filter(_.isInstanceOf[GeneralAssertionNode])
      val assumes = nodes.filter(n => !n.isClosed && n.isInstanceOf[GeneralAssumptionNode] && !n.isInstanceOf[LabelNode])
      addTransitiveEdges(asserts, assumes)
      val checks = asserts.filter(_.isInstanceOf[SimpleCheckNode])
      val notChecks = nodes.filter(n => !n.isClosed && !n.isInstanceOf[SimpleCheckNode])
      addTransitiveEdges(checks, notChecks)
    }
  }

  private def removeAllEdgesForNode(node: DependencyAnalysisNode): Unit = {
    val id = node.id
    val predecessors = (edges filter { case (_, t) => t.contains(id) }).keys
    val successors = edges.getOrElse(id, Set.empty)
    edges.remove(id)
    predecessors foreach (pid => edges.update(pid, edges.getOrElse(pid, Set.empty).filter(_ != id) ++ successors))
  }

  // TODO ake: maybe move to DependencyAnalyzer?
  def removeLabelNodes(): Unit = {
    def filterCriteria(n: DependencyAnalysisNode) = n.isInstanceOf[LabelNode]

    assumptionNodes filter filterCriteria foreach removeAllEdgesForNode
    assumptionNodes = assumptionNodes filterNot filterCriteria
  }

  def removeInternalNodes(): Unit = {
    def filterCriteria(n: DependencyAnalysisNode) = AssumptionType.internalTypes.contains(n.assumptionType)

    assumptionNodes filter filterCriteria foreach removeAllEdgesForNode
    assumptionNodes = assumptionNodes filterNot filterCriteria
  }

  def exportGraph(dirName: String): Unit = {
    val directory = Paths.get(dirName).toFile
    directory.mkdir()
    exportNodes(dirName + "/nodes.csv")
    exportEdges(dirName + "/edges.csv")
  }

  private def exportEdges(fileName: String): Unit = {
    val writer = new PrintWriter(fileName)
    writer.println("source,target,label")
    edges foreach (e => e._2 foreach (s => writer.println(s.toString + "," + e._1.toString + ",direct")))
    writer.close()
  }

  private def exportNodes(fileName: String): Unit = {
    val sep = "#"
    def getNodeExportString(node: DependencyAnalysisNode): String = {
      val parts = mutable.Seq(node.id.toString, node.getNodeType, node.assumptionType.toString, node.getNodeString, node.sourceInfo.toString, node.sourceInfo.getPositionString, node.sourceInfo.getFineGrainedSource.toString)
      parts.map(_.replace("#", "@")).mkString(sep)
    }
    val writer = new PrintWriter(fileName)
    val headerParts = mutable.Seq("id", "node type", "assumption type", "node info", "source info", "position", "fine grained source")
    writer.println(headerParts.mkString(sep))
    getNodes foreach (n => writer.println(getNodeExportString(n).replace("\n", " ")))
    writer.close()
  }
}


