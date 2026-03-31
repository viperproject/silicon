package viper.silicon.dependencyAnalysis

import viper.silver.dependencyAnalysis.{AbstractReadOnlyDependencyGraph, AssumptionType}

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
  def getEdgesConnectingMethodsDownwards: Map[Int, Set[Int]]
  def getEdgesConnectingMethodsUpwards: Map[Int, Set[Int]]
  def getAllEdges: Map[Int, Set[Int]] // target -> direct dependencies
  def getAllEdges(includeUpwardEdges: Boolean, includeDownwardEdges: Boolean): Map[Int, Set[Int]] // target -> direct dependencies

  @deprecated // needs to be adapted to the notion of upward and downward edges
  def existsAnyDependency(sources: Set[Int], targets: Set[Int], includeInfeasibilityNodes: Boolean): Boolean
  def getAllDependencies(sources: Set[Int], includeInfeasibilityNodes: Boolean, includeUpwardEdges: Boolean, includeDownwardEdges: Boolean): Set[Int]
  def getAllDependents(sources: Set[Int], includeInfeasibilityNodes: Boolean, includeUpwardEdges: Boolean, includeDownwardEdges: Boolean): Set[Int]

  def exportGraph(dirName: String): Unit
}

class DependencyGraph extends ReadOnlyDependencyGraph {
  private var assumptionNodes: mutable.Seq[GeneralAssumptionNode] = mutable.Seq()
  private var assertionNodes: mutable.Seq[GeneralAssertionNode] = mutable.Seq()
  private val edges: mutable.Map[Int, Set[Int]] = mutable.Map.empty
  private val edgesConnectingMethodsDownwards: mutable.Map[Int, Set[Int]] = mutable.Map.empty // keep this, it's relevant for computing verification progress
  private val edgesConnectingMethodsUpwards: mutable.Map[Int, Set[Int]] = mutable.Map.empty // keep this, it's relevant for computing verification progress
  private var vacuousProofs: mutable.Seq[Int] = mutable.Seq()

  def getNodes: Seq[DependencyAnalysisNode] = getAssumptionNodes ++ getAssertionNodes
  def getAssumptionNodes: Seq[GeneralAssumptionNode] = assumptionNodes.toSeq
  def getAssertionNodes: Seq[GeneralAssertionNode] = assertionNodes.toSeq
  def getDirectEdges: Map[Int, Set[Int]] = edges.toMap
  def getEdgesConnectingMethodsDownwards: Map[Int, Set[Int]] = edgesConnectingMethodsDownwards.toMap
  def getEdgesConnectingMethodsUpwards: Map[Int, Set[Int]] = edgesConnectingMethodsUpwards.toMap

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
    val keys = intraMethodEdges.keySet ++ edgesConnectingMethodsDownwards.keySet ++ edgesConnectingMethodsUpwards.keySet
    val allEdges = mutable.Map[Int, Set[Int]]()
    keys foreach {key =>
      allEdges.update(key, intraMethodEdges.getOrElse(key, Set()) ++ edgesConnectingMethodsDownwards.getOrElse(key, Set()) ++ edgesConnectingMethodsUpwards.getOrElse(key, Set()))
    }
    allEdges.toMap
  }

  def getAllEdges(includeDownwardEdges: Boolean, includeUpwardEdges: Boolean): Map[Int, Set[Int]] = {
    val intraMethodEdges = getIntraMethodEdges
    val upwardEdges: mutable.Map[Int, Set[Int]] = if(includeUpwardEdges) edgesConnectingMethodsUpwards else mutable.Map.empty
    val downwardEdges: mutable.Map[Int, Set[Int]]  = if(includeDownwardEdges) edgesConnectingMethodsDownwards else mutable.Map.empty
    val keys = intraMethodEdges.keySet ++ downwardEdges.keySet ++ upwardEdges.keySet
    val allEdges = mutable.Map[Int, Set[Int]]()
    keys foreach {key =>
      allEdges.update(key, intraMethodEdges.getOrElse(key, Set()) ++ downwardEdges.getOrElse(key, Set()) ++ upwardEdges.getOrElse(key, Set()))
    }
    allEdges.toMap
  }

  def getVacuousProofs: Set[Int] = vacuousProofs.toSet // TODO ake: what to do with these?

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

  def addEdgesConnectingMethodsDownwards(sources: Iterable[Int], target: Int): Unit = {
    val oldSources = edgesConnectingMethodsDownwards.getOrElse(target, Set.empty)
    val newSources = sources.filter(_ != target)
    if(newSources.nonEmpty)
      edgesConnectingMethodsDownwards.update(target, oldSources ++ newSources)
  }

  def addEdgesConnectingMethodsDownwards(sources: Iterable[Int], targets: Iterable[Int]): Unit = {
    targets foreach (addEdgesConnectingMethodsDownwards(sources, _))
  }

  def addEdgesConnectingMethodsDownwards(source: Int, targets: Iterable[Int]): Unit = {
    addEdgesConnectingMethodsDownwards(Set(source), targets)
  }

  def addEdgesConnectingMethodsUpwards(sources: Iterable[Int], target: Int): Unit = {
    val oldSources = edgesConnectingMethodsUpwards.getOrElse(target, Set.empty)
    val newSources = sources.filter(_ != target)
    if(newSources.nonEmpty)
      edgesConnectingMethodsUpwards.update(target, oldSources ++ newSources)
  }

  def addEdgesConnectingMethodsUpwards(sources: Iterable[Int], targets: Iterable[Int]): Unit = {
    targets foreach (addEdgesConnectingMethodsUpwards(sources, _))
  }

  def addEdgesConnectingMethodsUpwards(source: Int, targets: Iterable[Int]): Unit = {
    addEdgesConnectingMethodsUpwards(Set(source), targets)
  }


  def addVacuousProof(assertionId: Int): Unit = {
    vacuousProofs = assertionId +: vacuousProofs
  }

  @deprecated // needs to be adapted to the notion of upward and downward edges
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

  def getAllDependencies(targets: Set[Int], includeInfeasibilityNodes: Boolean, includeUpwardEdges: Boolean, includeDownwardEdges: Boolean): Set[Int] = {
    val infeasibilityNodeIds: Set[Int] = if(includeInfeasibilityNodes) Set.empty else (getAssumptionNodes filter (_.isInstanceOf[InfeasibilityNode]) map (_.id)).toSet
    var visited: Set[Int] = Set.empty
    var queue: List[Int] = targets.toList
    val allEdges = getAllEdges(includeDownwardEdges, includeUpwardEdges)
    while(queue.nonEmpty){
      val curr = queue.head
      val newVisits = allEdges.getOrElse(curr, Set()).diff(infeasibilityNodeIds)
      visited = visited ++ Set(curr)
      queue = queue.tail ++ (newVisits filter (!visited.contains(_)))
    }
    visited
  }

  def getAllDependents(sources: Set[Int], includeInfeasibilityNodes: Boolean, includeUpwardEdges: Boolean, includeDownwardEdges: Boolean): Set[Int] = {
    val infeasibilityNodeIds: Set[Int] = if(includeInfeasibilityNodes) Set.empty else (getAssumptionNodes filter (_.isInstanceOf[InfeasibilityNode]) map (_.id)).toSet
    var visited: Set[Int] = Set.empty
    var queue: Set[Int] = sources
    val allEdges = getAllEdges(includeDownwardEdges, includeUpwardEdges)
    while(queue.nonEmpty){
      val newVisits = allEdges.filter{case (t, s) => s.intersect(queue).nonEmpty && !infeasibilityNodeIds.contains(t)}.keys.toSet
      visited = visited ++ queue
      queue = newVisits diff visited
    }
    visited
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
    def filterCriteria(n: DependencyAnalysisNode) = AssumptionType.internalTypes.contains(n.assumptionType) && !AssumptionType.CustomInternal.equals(n.assumptionType)

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
    val builder = new StringBuilder()
    getDirectEdges foreach (e => e._2 foreach (s => builder.append(s.toString + "," + e._1.toString + ",direct" + "\n")))
    getEdgesConnectingMethodsDownwards foreach (e => e._2 foreach (s => builder.append(s.toString + "," + e._1.toString + ",interprocedural downward" + "\n")))
    getEdgesConnectingMethodsUpwards foreach (e => e._2 foreach (s => builder.append(s.toString + "," + e._1.toString + ",interprocedural upward" + "\n")))

    val writer = new PrintWriter(fileName)
    writer.println("source,target,label")
    writer.println(builder.toString())
    writer.close()
  }

  private def exportNodes(fileName: String): Unit = {
    val sep = "#"
    def getNodeExportString(node: DependencyAnalysisNode): String = {
      val parts = mutable.Seq(node.id.toString, node.getNodeType, node.assumptionType.toString, node.getNodeString, node.sourceInfo.toString, node.sourceInfo.getPositionString, node.sourceInfo.toString /* TODO ake: merge info */, node.sourceInfo.getDescription)
      parts.map(_.replace("#", "@")).mkString(sep)
    }
    val headerParts = mutable.Seq("id", "node type", "assumption type", "node info", "source info", "position", "fine grained source", "description")
    val builder = new StringBuilder()
    getNodes foreach (n => builder.append(getNodeExportString(n).replace("\n", " ") + "\n"))

    val writer = new PrintWriter(fileName)
    writer.println(headerParts.mkString(sep))
    writer.println(builder.result())
    writer.close()
  }
}


