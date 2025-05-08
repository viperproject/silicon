package viper.silicon.assumptionAnalysis

import viper.silicon.interfaces.state.Chunk
import viper.silicon.state.terms.Term
import viper.silver.ast

import java.util.concurrent.atomic.AtomicInteger
import scala.collection.mutable

object AssumptionType extends Enumeration {
  type AssumptionType = Value
  val Explicit, PathCondition, Implicit, Unknown = Value
}
import AssumptionType._

// TODO ake: make sure that the string does not contain invalid characters
class AssumptionLabel(description: String, id: Option[Int], offset: Int = 0) {
  override def toString: String =
    if(id.isDefined) description.trim + "_" + id.get + "_" + offset
    else ""
}


object AssumptionAnalysisGraphHelper {
  private val idCounter: AtomicInteger = new AtomicInteger(0)

  def nextId(): Int = {
    idCounter.getAndIncrement()
  }
}

trait AssumptionAnalysisGraph {
  var nodes: Seq[AssumptionAnalysisNode]

  // TODO ake
  // var groups: mutable.Map[GroupNode, Set[Int]] // e.g. statements -> assumptions/assertions

  var edges: mutable.Map[Int, Set[Int]] // e.g. assertion -> assumptions

  def addNode(node: AssumptionAnalysisNode): Unit
  def addNodes(nodes: Set[AssumptionAnalysisNode]): Unit
  def addEdges(source: Int, targets: Iterable[Int]): Unit
  def addEdges(sources: Iterable[Int], target: Int): Unit

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
    sources.foreach(addEdges(_, Set(target)))
  }
}

trait AssumptionAnalysisNode {
  val id: Int = AssumptionAnalysisGraphHelper.nextId()
  val assumptionType: AssumptionType

  def equals(other: AssumptionAnalysisNode): Boolean

  override def toString: String = id.toString

  def isIncludedInAnalysis: Boolean = assumptionType match {
    case Explicit => true
    case PathCondition => true
    case Implicit => true
    case Unknown => true
  }
}


trait ChunkAnalysisInfo {
  val chunk: Chunk

  override def toString: String = super.toString + " with chunk " + chunk.toString

  def getChunk: Chunk = chunk
}

class SimpleAssumptionNode(assumption: ast.Exp, val assumptionType: AssumptionType = Unknown) extends AssumptionAnalysisNode {

  override def toString: String = super.toString + ": " + assumption.toString

  def getAssumption: ast.Exp = assumption

  override def equals(other: AssumptionAnalysisNode): Boolean = {
    other match {
      case node: SimpleAssumptionNode =>
        node.getAssumption.equals(this.assumption) && node.getAssumption.pos.equals(this.assumption.pos)
      case _ => false
    }
  }
}

// TODO ake: remove this
class StringAssumptionNode(description: String, val assumptionType: AssumptionType = Unknown) extends AssumptionAnalysisNode {

  override def toString: String = super.toString + ": " + description

  def getAssumption: String = description

  override def equals(other: AssumptionAnalysisNode): Boolean = {
    other.id == this.id
  }
}

// TODO ake: ast.Exp instead of Term
class SimpleAssertionNode(assertion: Term) extends AssumptionAnalysisNode {
  override val assumptionType: AssumptionType = AssumptionType.Explicit
  override def toString: String = super.toString + ": " + assertion.toString

  def getAssertion: Term = assertion

  override def equals(other: AssumptionAnalysisNode): Boolean = {
    other match {
      case node: SimpleAssertionNode => node.getAssertion.equals(this.assertion)
      case _ => false
    }
  }
}

class PermissionAssumptionNode(assumption: ast.Exp, val chunk: Chunk, assumptionType: AssumptionType = Unknown) extends SimpleAssumptionNode(assumption, assumptionType) with ChunkAnalysisInfo {
  override def equals(other: AssumptionAnalysisNode): Boolean = {
    other match {
      case node: PermissionAssumptionNode =>
        node.getChunk.equals(this.chunk) && super.equals(other)
      case _ => false
    }
  }
}

class PermissionAssertionNode(assertion: Term, val chunk: Chunk, assumptionType: AssumptionType = Unknown) extends SimpleAssertionNode(assertion) with ChunkAnalysisInfo {
  override def equals(other: AssumptionAnalysisNode): Boolean = {
    other match {
      case node: PermissionAssertionNode =>
        node.getChunk.equals(this.chunk) && super.equals(other)
      case _ => false
    }
  }
}

class ChunkGroupNode(description: String, val chunk: Chunk, val assumptionType: AssumptionType = Unknown) extends AssumptionAnalysisNode with ChunkAnalysisInfo {
  override def toString: String = description + " - " + super.toString


  override def equals(other: AssumptionAnalysisNode): Boolean = {
    other match {
      case node: ChunkAnalysisInfo =>
        node.getChunk.equals(this.chunk)
      case _ => false
    }
  }
}

//class StatementGroupNode(stmt: ast.Stmt, nodes: Set[AssumptionAnalysisNode], val assumptionType: AssumptionType) extends AssumptionAnalysisNode {
//  override def toString: String = super.toString + ": " + stmt.toString + " --> " + nodes.mkString(" && ")
//
//  def getStmt: ast.Stmt = stmt
//
//  override def equals(other: AssumptionAnalysisNode): Boolean = {
//    other match {
//      case node: StatementGroupNode =>
//        node.getStmt.equals(this.stmt) && node.getStmt.pos.equals(this.stmt.pos)
//      case _ => false
//    }
//  }
//}
