package viper.silicon.assumptionAnalysis

import viper.silicon.assumptionAnalysis.AssumptionType._
import viper.silicon.interfaces.state.Chunk
import viper.silicon.state.terms.Term
import viper.silver.ast

import java.io.{File, PrintWriter}
import java.util.concurrent.atomic.AtomicInteger
import scala.collection.mutable


object AssumptionAnalysisGraphHelper {
  private val idCounter: AtomicInteger = new AtomicInteger(0)

  def nextId(): Int = {
    idCounter.getAndIncrement()
  }
}

trait AssumptionAnalysisGraph {
  var nodes: Seq[AssumptionAnalysisNode]
  var edges: mutable.Map[Int, Set[Int]]
  var transitiveEdges: mutable.Map[Int, Set[Int]] = mutable.Map.empty

  def addNode(node: AssumptionAnalysisNode): Unit
  def addNodes(nodes: Set[AssumptionAnalysisNode]): Unit
  def addEdges(source: Int, targets: Iterable[Int]): Unit
  def addEdges(sources: Iterable[Int], target: Int): Unit
  def addEdges(sources: Iterable[Int],  targets: Iterable[Int]): Unit

  def getExplicitAndAssertNodesOnly(): Seq[AssumptionAnalysisNode] = {
    nodes.filter(n => n.assumptionType.equals(AssumptionType.Explicit) || n.isInstanceOf[GeneralAssertionNode])
  }

  def getImplicitNodesOnly(): Seq[AssumptionAnalysisNode] = {
    getNodesByAssumptionType(AssumptionType.Implicit)
  }

  def getNodesByAssumptionType(assumptionType: AssumptionType): Seq[AssumptionAnalysisNode] = {
    nodes.filter(n => n.assumptionType.equals(assumptionType))
  }

  def getNodesPerChunk(): mutable.HashMap[Chunk, Seq[AssumptionAnalysisNode]] = {
    val res = new mutable.HashMap[Chunk, Seq[AssumptionAnalysisNode]]()
    nodes filter (_.isInstanceOf[ChunkAnalysisInfo]) foreach {n =>
      res.updateWith(n.asInstanceOf[ChunkAnalysisInfo].getChunk)({
        case Some(ns) => Some(ns ++ Seq(n))
        case None => Some(Seq(n))
      })
    }
    res
  }

  def getNodesPerSourceInfo(): mutable.HashMap[AnalysisSourceInfo, Seq[AssumptionAnalysisNode]] = {
    val res = new mutable.HashMap[AnalysisSourceInfo, Seq[AssumptionAnalysisNode]]()
    nodes foreach {n =>
      res.updateWith(n.sourceInfo.getTopLevelSource)({
        case Some(ns) => Some(ns ++ Seq(n))
        case None => Some(Seq(n))
      })
    }
    res
  }

  def addTransitiveEdges(source: AssumptionAnalysisNode, targets: Iterable[AssumptionAnalysisNode]): Unit = {
    val oldTargets = transitiveEdges.getOrElse(source.id, Set.empty)
    val newTargets = targets filter(t => t.id > source.id) map(_.id) // we only want forward edges
    if(newTargets.nonEmpty) transitiveEdges.update(source.id, oldTargets ++ newTargets)
  }

  def addTransitiveEdges(source: Iterable[AssumptionAnalysisNode], targets: Iterable[AssumptionAnalysisNode]): Unit = {
    source foreach (s => addTransitiveEdges(s, targets))
  }

  def addTransitiveEdges(): Unit = {
    val nodesPerSourceInfo = getNodesPerSourceInfo()
    nodesPerSourceInfo foreach {nodes =>
      val asserts = nodes._2.filter(_.isInstanceOf[GeneralAssertionNode])
      val assumes = nodes._2.filter(_.isInstanceOf[GeneralAssumptionNode])
      addTransitiveEdges(asserts, assumes)
      val checks = asserts.filter(_.isInstanceOf[SimpleCheckNode])
      val notChecks = nodes._2.filter(!_.isInstanceOf[SimpleCheckNode])
      addTransitiveEdges(checks, notChecks)
    }
  }

  def exportGraph(fileName: String): Unit = {
    val directory = new File(fileName)
    directory.mkdir()
    exportNodes(fileName)
    exportEdges(fileName + "/edges.csv")
  }

  def exportEdges(fileName: String): Unit = {
    val writer = new PrintWriter(fileName)
    writer.println("source,target,label")
    edges foreach (e => e._2 foreach (t => writer.println(e._1 + "," + t + ",direct")))
    transitiveEdges foreach (e => e._2 foreach (t => writer.println(e._1 + "," + t + ",transitive")))
    writer.close()
  }

  private def exportNodes(fileName: String): Unit = {
    val sep = "#"
    def getNodeExportString(node: AssumptionAnalysisNode): String = {
      val parts = Seq(node.id.toString, node.getNodeType, node.assumptionType.toString, node.getNodeString, node.sourceInfo.toString, node.sourceInfo.getStringForExport, node.sourceInfo.getFineGrainedSource.toString)
      parts.map(_.replace("#", "@")).mkString(sep)
    }
    val writer = new PrintWriter(fileName + "/nodes.csv")
    val headerParts = Seq("id", "node type", "assumption type", "node info", "source info", "position", "fine grained source")
    writer.println(headerParts.mkString(sep))
    nodes foreach (n => writer.println(getNodeExportString(n).replace("\n", " ")))
    writer.close()
  }
}


class DefaultAssumptionAnalysisGraph extends AssumptionAnalysisGraph {
  override var nodes: Seq[AssumptionAnalysisNode] = Seq()
  override var edges: mutable.Map[Int, Set[Int]] = mutable.Map.empty

  override def addNode(node: AssumptionAnalysisNode): Unit = {
    nodes = nodes :+ node
  }

  override def addNodes(nodes: Set[AssumptionAnalysisNode]): Unit = {
    nodes foreach addNode
  }

  override def addEdges(source: Int, targets: Iterable[Int]): Unit = {
    val oldTargets = edges.getOrElse(source, Set.empty)
    val newTargets = targets filter(t => t > source) // only forward edges
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

  override def toString: String = id.toString + " | " + getNodeString + " | " + sourceInfo.toString

  def getNodeString: String
  def getNodeType: String
}

trait GeneralAssumptionNode extends AssumptionAnalysisNode {
  override def getNodeType: String = "Assumption"
}
trait GeneralAssertionNode extends AssumptionAnalysisNode {
  override def getNodeType: String = "Assertion"
   var isAsserted = false
}

trait ChunkAnalysisInfo {
  val chunk: Chunk
  val permAmount: Option[ast.Exp]
  def getChunk: Chunk = chunk
}

case class SimpleAssumptionNode(assumption: ast.Exp, sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType = Unknown) extends GeneralAssumptionNode {
  override def getNodeString: String ="assume " + assumption.toString
}

case class StringAssumptionNode(description: String, sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType = Unknown) extends GeneralAssumptionNode {
  override def getNodeString: String = "assume " + description
}

case class SimpleAssertionNode(assertion: ast.Exp, sourceInfo: AnalysisSourceInfo) extends GeneralAssertionNode {
  val assumptionType: AssumptionType = Explicit
  override def getNodeString: String = "assert " + assertion.toString
}

case class StringAssertionNode(description: String, sourceInfo: AnalysisSourceInfo) extends GeneralAssertionNode {
  val assumptionType: AssumptionType = Explicit
  override def getNodeString: String = "assert " + description
}

case class SimpleCheckNode(t: Term, sourceInfo: AnalysisSourceInfo) extends GeneralAssertionNode {
  val assumptionType: AssumptionType = Internal
  override def getNodeString: String = "check " + t
  override def getNodeType: String = "Check"
}

case class PermissionInhaleNode(chunk: Chunk, permAmount: Option[ast.Exp], sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType = Unknown) extends GeneralAssumptionNode with ChunkAnalysisInfo {
  override def getNodeString: String = "inhale " + chunk.getAnalysisInfo
  override def getNodeType: String = "Inhale"
}

case class PermissionExhaleNode(chunk: Chunk, permAmount: Option[ast.Exp], sourceInfo: AnalysisSourceInfo) extends GeneralAssertionNode with ChunkAnalysisInfo {
  isAsserted = true
  val assumptionType: AssumptionType = Explicit
  override def getNodeType: String = "Exhale"
  override def getNodeString: String = "exhale " + chunk.getAnalysisInfo
}

case class PermissionAssertNode(chunk: Chunk, permAmount: Option[ast.Exp], sourceInfo: AnalysisSourceInfo) extends GeneralAssertionNode with ChunkAnalysisInfo {
  isAsserted = true
  val assumptionType: AssumptionType = Explicit
  override def getNodeString: String = "assert " + permAmount.getOrElse("") + " for " + chunk.getAnalysisInfo
}

