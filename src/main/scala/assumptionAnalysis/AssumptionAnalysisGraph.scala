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
  def getDirectEdges: Map[Int, Set[Int]]
  def getTransitiveEdges: Map[Int, Set[Int]]
  def getAllEdges: Map[Int, Set[Int]]

  def existsAnyDependency(sources: Set[Int], targets: Set[Int]): Boolean

  def exportGraph(dirName: String): Unit
}

class AssumptionAnalysisGraph extends ReadOnlyAssumptionAnalysisGraph {
  var nodes: mutable.Seq[AssumptionAnalysisNode] = mutable.Seq()
  private val edges: mutable.Map[Int, Set[Int]] = mutable.Map.empty
  private val transitiveEdges: mutable.Map[Int, Set[Int]] = mutable.Map.empty

  def getNodes: Seq[AssumptionAnalysisNode] = nodes.toSeq
  def getDirectEdges: Map[Int, Set[Int]] = edges.toMap
  def getTransitiveEdges: Map[Int, Set[Int]] = transitiveEdges.toMap
  def getAllEdges: Map[Int, Set[Int]] = (edges ++ transitiveEdges).toMap

  def addNode(node: AssumptionAnalysisNode): Unit = {
    nodes = nodes :+ node
  }

  def addNodes(nodes: Iterable[AssumptionAnalysisNode]): Unit = {
    nodes foreach addNode
  }

  def addEdges(source: Int, targets: Iterable[Int]): Unit = {
    val oldTargets = edges.getOrElse(source, Set.empty)
    val newTargets = targets.filter(_ != source)
    if(newTargets.nonEmpty)
      edges.update(source, oldTargets ++ newTargets)
  }

  def addEdges(sources: Iterable[Int], target: Int): Unit = {
    addEdges(sources, Set(target))
  }

  def addEdges(sources: Iterable[Int], targets: Iterable[Int]): Unit = {
    sources foreach (addEdges(_, targets))
  }

  def existsAnyDependency(sources: Set[Int], targets: Set[Int]): Boolean = {
    var visited: Set[Int] = sources
    var queue: List[Int] = sources.toList
    while(queue.nonEmpty){
      val curr = queue.head
      val newVisits = edges.getOrElse(curr, Set()) ++ transitiveEdges.getOrElse(curr, Set())
      if(newVisits.intersect(targets).nonEmpty)
        return true
      visited = visited ++ Set(curr)
      queue = queue.tail ++ (newVisits filter (!visited.contains(_)))
    }
    false
  }

  private def addTransitiveEdges(source: AssumptionAnalysisNode, targets: Iterable[AssumptionAnalysisNode]): Unit = {
    val oldTargets = transitiveEdges.getOrElse(source.id, Set.empty)
    val newTargets = targets map(_.id) // filter(_ > source.id) does not work due to loop invariants
    if(newTargets.nonEmpty) transitiveEdges.update(source.id, oldTargets ++ newTargets)
  }

  private def addTransitiveEdges(source: Iterable[AssumptionAnalysisNode], targets: Iterable[AssumptionAnalysisNode]): Unit = {
    source foreach (s => addTransitiveEdges(s, targets))
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
    addEdges(predecessors, successors)
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


