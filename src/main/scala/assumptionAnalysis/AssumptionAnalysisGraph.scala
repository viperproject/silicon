package viper.silicon.assumptionAnalysis

import viper.silicon.interfaces.state.Chunk
import viper.silver.ast

import java.util.concurrent.atomic.AtomicInteger
import scala.collection.mutable

object AssumptionType extends Enumeration {
  type AssumptionType = Value
  val Explicit, PathCondition, Internal, Implicit, Assertion, Unknown = Value
}
import viper.silicon.assumptionAnalysis.AssumptionType._


object AssumptionAnalysisGraphHelper {
  private val idCounter: AtomicInteger = new AtomicInteger(0)

  def nextId(): Int = {
    idCounter.getAndIncrement()
  }
}

trait AssumptionAnalysisGraph {
  var nodes: Seq[AssumptionAnalysisNode]
  var edges: mutable.Map[Int, Set[Int]]

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

  // def findDependentAssumptions(assertion, enableTransitivity=false)
  // def findDependentAssertions(assumption, enableTransitivity=false)
  // def findUnnecessaryAssumptions(enableTransitivity=false)
  // def mergeIdenticalNodes()
}


class DefaultAssumptionAnalysisGraph extends AssumptionAnalysisGraph {
  override var nodes: Seq[AssumptionAnalysisNode] = Seq()
  override var edges: mutable.Map[Int, Set[Int]] = mutable.Map.empty

  override def addNode(node: AssumptionAnalysisNode): Unit = {
    val identicalNodes = nodes.filter(node.equals) // TODO ake: when to merge identical nodes?
    nodes = nodes :+ node
  }

  override def addNodes(nodes: Set[AssumptionAnalysisNode]): Unit = {
    nodes foreach addNode
  }

  override def addEdges(source: Int, targets: Iterable[Int]): Unit = {
    val oldTargets = edges.getOrElse(source, Set.empty)
    edges.update(source, oldTargets ++ targets)
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

  override def toString: String = id.toString + ": " + getNodeString + " at " + sourceInfo.toString

  def getNodeString: String

  def isIncludedInAnalysis: Boolean = assumptionType match {
    case Explicit => true
    case PathCondition => true
    case Internal => true
    case Implicit => true
    case Unknown => true
  }
}

trait GeneralAssumptionNode extends AssumptionAnalysisNode {}
trait GeneralAssertionNode extends AssumptionAnalysisNode {}

trait ChunkAnalysisInfo {
  val chunk: Chunk

  def getChunk: Chunk = chunk
}

case class SimpleAssumptionNode(assumption: ast.Exp, sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType = Unknown) extends GeneralAssumptionNode {
  override def getNodeString: String ="assume " + assumption.toString
}

case class StringAssumptionNode(description: String, sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType = Unknown) extends GeneralAssumptionNode {
  override def getNodeString: String = "assume " + description
}

case class SimpleAssertionNode(assertion: ast.Exp, isAsserted: Boolean, sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType = Explicit) extends GeneralAssertionNode {
  override def getNodeString: String = "assert " + assertion.toString
}

case class StringAssertionNode(description: String, isAsserted: Boolean, sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType = Explicit) extends GeneralAssertionNode {
  override def getNodeString: String = "assert " + description
}

case class PermissionInhaleNode(chunk: Chunk, sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType = Unknown) extends GeneralAssumptionNode with ChunkAnalysisInfo {
  override def getNodeString: String = "inhale " + chunk.toString
}

case class PermissionExhaleNode(chunk: Chunk, sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType = Explicit) extends GeneralAssertionNode with ChunkAnalysisInfo {
  override def getNodeString: String = "exhale " + chunk.toString
}

case class PermissionAssertNode(chunk: Chunk, sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType = Explicit) extends GeneralAssertionNode with ChunkAnalysisInfo {
  override def getNodeString: String = "assert " + chunk.toString
}



