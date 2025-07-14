package viper.silicon.assumptionAnalysis

import viper.silicon.assumptionAnalysis.AssumptionType.AssumptionType
import viper.silicon.interfaces.state.Chunk
import viper.silicon.state.terms.{False, Term, True}
import viper.silver.ast.Position

import java.io.{File, PrintWriter}
import java.util.concurrent.atomic.AtomicInteger
import scala.collection.mutable
import scala.collection.mutable.Seq


object AssumptionAnalysisGraphHelper {
  private val idCounter: AtomicInteger = new AtomicInteger(0)

  def nextId(): Int = {
    idCounter.getAndIncrement()
  }
}

trait AssumptionAnalysisGraph {
  var nodes: mutable.Seq[AssumptionAnalysisNode]
  var edges: mutable.Map[Int, Set[Int]]
  var transitiveEdges: mutable.Map[Int, Set[Int]] = mutable.Map.empty

  def addNode(node: AssumptionAnalysisNode): Unit
  def addNodes(nodes: Iterable[AssumptionAnalysisNode]): Unit
  def addEdges(source: Int, targets: Iterable[Int]): Unit
  def addEdges(sources: Iterable[Int], target: Int): Unit
  def addEdges(sources: Iterable[Int],  targets: Iterable[Int]): Unit

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

  def getAllNonInternalDependencies(nodeIdsToAnalyze: Set[Int]): Set[AssumptionAnalysisNode] = {
    nodes.filter(node =>
      ((node.isInstanceOf[GeneralAssumptionNode] && !node.assumptionType.equals(AssumptionType.Internal)) ||
        (node.isInstanceOf[GeneralAssertionNode] && node.assumptionType.equals(AssumptionType.Postcondition))
        || node.isInstanceOf[InfeasibilityNode]) &&
        existsAnyDependency(Set(node.id), nodeIdsToAnalyze)).toSet
  }

  private def getNodesByProperties(nodeType: Option[String], assumptionType: Option[AssumptionType], sourceInfo: Option[String], position: Option[Position]): mutable.Seq[AssumptionAnalysisNode] = {
    nodes filter (node =>
      nodeType.forall(node.getNodeType.equals) &&
      assumptionType.forall(node.assumptionType.equals) &&
      sourceInfo.forall(node.sourceInfo.toString.equals) &&
      position.forall(node.sourceInfo.getPosition.equals)
      )
  }

  def getExplicitAssertionNodes: Set[AssumptionAnalysisNode] = {
    (getNodesByProperties(Some("Assertion"), Some(AssumptionType.Explicit), None, None) ++
    getNodesByProperties(Some("Assertion"), Some(AssumptionType.Postcondition), None, None) ++
      getNodesByProperties(Some("Exhale"), Some(AssumptionType.Explicit), None, None) ++
      getNodesByProperties(Some("Exhale"), Some(AssumptionType.Postcondition), None, None)).toSet
  }

  def getNonInternalAssumptionNodesPerSource: Map[String, mutable.Seq[AssumptionAnalysisNode]] = {
    getNodesPerSourceInfo filter {case (_, nodes) =>
      nodes exists (node =>
        node.isInstanceOf[GeneralAssumptionNode] &&
        !node.assumptionType.equals(AssumptionType.Internal) &&
        !node.assumptionType.equals(AssumptionType.Axiom))
    }
  }


  def getNodesPerChunk: Map[Chunk, mutable.Seq[AssumptionAnalysisNode]] = {
    nodes.filter (_.isInstanceOf[ChunkAnalysisInfo])
      .groupBy(_.asInstanceOf[ChunkAnalysisInfo].getChunk)
  }

  def getNodesPerTransitivitySourceInfo: Map[String, mutable.Seq[AssumptionAnalysisNode]] = {
    nodes.groupBy(_.sourceInfo.getSourceForTransitiveEdges.toString)
  }

  private def getNodesPerSourceInfo: Map[String, mutable.Seq[AssumptionAnalysisNode]] = {
    nodes.groupBy(_.sourceInfo.getTopLevelSource.toString)
  }

  private def addTransitiveEdges(source: AssumptionAnalysisNode, targets: Iterable[AssumptionAnalysisNode]): Unit = {
    val oldTargets = transitiveEdges.getOrElse(source.id, Set.empty)
    val newTargets = targets map(_.id) // filter(_ > source.id) does not work due to loop invariants
    if(newTargets.nonEmpty) transitiveEdges.update(source.id, oldTargets ++ newTargets)
  }

  private def addTransitiveEdges(source: Iterable[AssumptionAnalysisNode], targets: Iterable[AssumptionAnalysisNode]): Unit = {
    source foreach (s => addTransitiveEdges(s, targets))
  }

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
    edges foreach (e => e._2 foreach (t => writer.println(e._1 + "," + t + ",direct")))
    transitiveEdges foreach (e => e._2 foreach (t => writer.println(e._1 + "," + t + ",transitive")))
    writer.close()
  }

  private def exportNodes(fileName: String): Unit = {
    val sep = "#"
    def getNodeExportString(node: AssumptionAnalysisNode): String = {
      val parts = Seq(node.id.toString, node.getNodeType, node.assumptionType.toString, node.getNodeString, node.sourceInfo.toString, node.sourceInfo.getPositionString, node.sourceInfo.getFineGrainedSource.toString)
      parts.map(_.replace("#", "@")).mkString(sep)
    }
    val writer = new PrintWriter(fileName)
    val headerParts = Seq("id", "node type", "assumption type", "node info", "source info", "position", "fine grained source")
    writer.println(headerParts.mkString(sep))
    nodes foreach (n => writer.println(getNodeExportString(n).replace("\n", " ")))
    writer.close()
  }

  def mergeNodesBySource(): AssumptionAnalysisGraph = {
    def keepNode(n: AssumptionAnalysisNode): Boolean = n.isClosed || n.isInstanceOf[InfeasibilityNode]
    val mergedGraph = new DefaultAssumptionAnalysisGraph
    val nodeMap = mutable.HashMap[Int, Int]()
    nodes.filter(keepNode).foreach{n =>
      nodeMap.put(n.id, n.id)
      mergedGraph.addNode(n)
    }

    val nodesBySource = nodes.filter(!keepNode(_))
      .groupBy(n => (n.sourceInfo.getSourceForTransitiveEdges.toString, n.sourceInfo.getTopLevelSource.toString, n.assumptionType))
    nodesBySource foreach {case ((_, _, assumptionType), nodes) =>
      val assumptionNodes = nodes.filter(_.isInstanceOf[GeneralAssumptionNode])
      if(assumptionNodes.nonEmpty) {
        val newNode = SimpleAssumptionNode(True, None, assumptionNodes.head.sourceInfo, assumptionType, isClosed = true)
        assumptionNodes foreach (n => nodeMap.put(n.id, newNode.id))
        mergedGraph.addNode(newNode)
      }
    }

    nodesBySource foreach {case ((_, _, assumptionType), nodes) =>
      val assertionNodes = nodes.filter(_.isInstanceOf[GeneralAssertionNode])
      if(assertionNodes.nonEmpty){
        val newNode = SimpleAssertionNode(True, assumptionType, assertionNodes.head.sourceInfo, isClosed=true)
        assertionNodes foreach (n => nodeMap.put(n.id, newNode.id))
        mergedGraph.addNode(newNode)
      }
    }

    (edges ++ transitiveEdges) foreach {case (source, targets) =>
      val newSource = nodeMap(source)
      mergedGraph.addEdges(newSource, targets.map(nodeMap(_)))
    }

    mergedGraph
  }
}


class DefaultAssumptionAnalysisGraph extends AssumptionAnalysisGraph {
  override var nodes: Seq[AssumptionAnalysisNode] = Seq()
  override var edges: mutable.Map[Int, Set[Int]] = mutable.Map.empty

  override def addNode(node: AssumptionAnalysisNode): Unit = {
    nodes = nodes :+ node
  }

  override def addNodes(nodes: Iterable[AssumptionAnalysisNode]): Unit = {
    nodes foreach addNode
  }

  override def addEdges(source: Int, targets: Iterable[Int]): Unit = {
    val oldTargets = edges.getOrElse(source, Set.empty)
    val newTargets = targets.filter(_ != source)
    if(newTargets.nonEmpty)
      edges.update(source, oldTargets ++ newTargets)
  }

  override def addEdges(sources: Iterable[Int], target: Int): Unit = {
    addEdges(sources, Set(target))
  }

  override def addEdges(sources: Iterable[Int], targets: Iterable[Int]): Unit = {
    sources foreach (addEdges(_, targets))
  }
}

trait AssumptionAnalysisNode {
  val id: Int = AssumptionAnalysisGraphHelper.nextId()
  val sourceInfo: AnalysisSourceInfo
  val assumptionType: AssumptionType
  val isClosed: Boolean
  val term: Term
  def getTerm: Term = term

  override def toString: String = id.toString + " | " + getNodeString + " | " + sourceInfo.toString

  def getNodeString: String
  def getNodeType: String
}

trait GeneralAssumptionNode extends AssumptionAnalysisNode {
  override def getNodeType: String = "Assumption"
}
trait GeneralAssertionNode extends AssumptionAnalysisNode {
  override def getNodeType: String = "Assertion"
}

trait ChunkAnalysisInfo {
  val chunk: Chunk
  def getChunk: Chunk = chunk
}

case class SimpleAssumptionNode(term: Term, description: Option[String], sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType, isClosed: Boolean) extends GeneralAssumptionNode {
  override def getNodeString: String = "assume " + term.toString + description.map(" (" + _ + ")").getOrElse("")
}

case class SimpleAssertionNode(term: Term, assumptionType: AssumptionType, sourceInfo: AnalysisSourceInfo, isClosed: Boolean) extends GeneralAssertionNode {
  override def getNodeString: String = "assert " + term.toString
}

case class SimpleCheckNode(term: Term, assumptionType: AssumptionType, sourceInfo: AnalysisSourceInfo, isClosed: Boolean) extends GeneralAssertionNode {
  override def getNodeString: String = "check " + term
  override def getNodeType: String = "Check"
}

case class PermissionInhaleNode(chunk: Chunk, term: Term, sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType, isClosed: Boolean, labelNode: LabelNode) extends GeneralAssumptionNode with ChunkAnalysisInfo {
  override def getNodeString: String = "inhale " + chunk.toString
  override def getNodeType: String = "Inhale"
}

case class PermissionExhaleNode(chunk: Chunk, term: Term, sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType, isClosed: Boolean) extends GeneralAssertionNode with ChunkAnalysisInfo {
  override def getNodeType: String = "Exhale"
  override def getNodeString: String = "exhale " + chunk.toString
}

case class LabelNode(term: Term) extends GeneralAssumptionNode {
  val sourceInfo: AnalysisSourceInfo = NoAnalysisSourceInfo()
  val assumptionType: AssumptionType = AssumptionType.Internal
  val isClosed: Boolean = true
  val description: String = term.toString
  override def getNodeType: String = "Label"
  override def getNodeString: String = "assume " + description
}

case class InfeasibilityNode(sourceInfo: AnalysisSourceInfo) extends AssumptionAnalysisNode {
  val term: Term = False
  val assumptionType: AssumptionType = AssumptionType.Implicit
  val isClosed: Boolean = true
  val description: String = "False"

  override def getNodeType: String = "Infeasible"
  override def getNodeString: String = "infeasible"
}

