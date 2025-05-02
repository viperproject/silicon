package assumptionAnalysis

import viper.silicon.state.terms.Term
import viper.silver.ast

import java.util.concurrent.atomic.AtomicInteger
import scala.collection.mutable

trait AssumptionAnalysisGraph {
  var nodes: mutable.Map[Int, AssumptionAnalysisNode]

  // TODO ake
  // var groups: mutable.Map[GroupNode, Set[Int]] // e.g. statements -> assumptions/assertions

  var edges: mutable.Map[Int, Set[Int]] // e.g. assertion -> assumptions

  def addNode(node: AssumptionAnalysisNode): Unit
  def addNodes(nodes: Set[AssumptionAnalysisNode]): Unit
  def createAndAddNode(assumptions: Set[ast.Exp], assertions: Set[Term]): Unit
  def addEdges(source: Int, targets: Set[Int]): Unit

  // def findDependentAssumptions(assertion, enableTransitivity=false)
  // def findDependentAssertions(assumption, enableTransitivity=false)
  // def findUnnecessaryAssumptions(enableTransitivity=false)
  // def mergeIdenticalNodes()
}

object AssumptionAnalysisGraphHelper {
  private val idCounter: AtomicInteger = new AtomicInteger(0)

  def nextId(): Int = {
    idCounter.getAndIncrement()
  }

  def createNode(assumptions: Set[ast.Exp], assertions: Set[Term]): Set[AssumptionAnalysisNode] = {
    (assumptions.size, assertions.size) match {
      case (0, _) => assertions.map(new SimpleAssertionNode(_))
      case (_, 0) => assumptions.map(new SimpleAssumptionNode(_))
      case (_, _) =>
        val a0 = assertions.map(new SimpleAssertionNode(_))
        val a1 = assumptions.map(new SimpleAssumptionNode(_))
        Set{new ComplexAssumptionNode(a0, a1)}
    }
  }
}

class DefaultAssumptionAnalysisGraph extends AssumptionAnalysisGraph {
  override var nodes: mutable.Map[Int, AssumptionAnalysisNode] = mutable.Map.empty
  override var edges: mutable.Map[Int, Set[Int]] = mutable.Map.empty

  override def addNode(node: AssumptionAnalysisNode): Unit = {
    val identicalNodes = nodes.values.filter(node.equals) // TODO ake: when to merge identical nodes?
    nodes.update(node.id, node)
  }

  override def addNodes(nodes: Set[AssumptionAnalysisNode]): Unit = {
    nodes foreach addNode
  }

  override def addEdges(source: Int, targets: Set[Int]): Unit = {
    val oldTargets = edges.getOrElse(source, Set.empty)
    edges.update(source, oldTargets ++ targets)
  }

  def createAndAddNode(assumptions: Set[ast.Exp], assertions: Set[Term]): Unit = {
    AssumptionAnalysisGraphHelper.createNode(assumptions, assertions).foreach(addNode)
  }
}

trait AssumptionAnalysisNode {
  val id: Int = AssumptionAnalysisGraphHelper.nextId()

  def equals(other: AssumptionAnalysisNode): Boolean
}

class SimpleAssumptionNode(assumption: ast.Exp) extends AssumptionAnalysisNode {

  override def toString: String = assumption.toString

  def getAssumption: ast.Exp = assumption

  override def equals(other: AssumptionAnalysisNode): Boolean = {
    other match {
      case node: SimpleAssumptionNode =>
        node.getAssumption.equals(this.assumption) && node.getAssumption.pos.equals(this.assumption.pos)
      case _ => false
    }
  }
}

// TODO ake: ast.Exp instead of Term
class SimpleAssertionNode(assertion: Term) extends AssumptionAnalysisNode {
  override def toString: String = assertion.toString

  def getAssertion: Term = assertion

  override def equals(other: AssumptionAnalysisNode): Boolean = {
    other match {
      case node: SimpleAssertionNode => node.getAssertion.equals(this.assertion)
      case _ => false
    }
  }
}

class StatementGroupNode(stmt: ast.Stmt, nodes: Set[AssumptionAnalysisNode]) extends AssumptionAnalysisNode {
  override def toString: String = stmt.toString + " --> " + nodes.mkString(" && ")

  def getStmt: ast.Stmt = stmt

  override def equals(other: AssumptionAnalysisNode): Boolean = {
    other match {
      case node: StatementGroupNode =>
        node.getStmt.equals(this.stmt) && node.getStmt.pos.equals(this.stmt.pos)
      case _ => false
    }
  }
}

// TODO ake: or maybe instead have an map from Stmt -> (Set[Int], Set[Int]) in Assumption Graph
class ComplexAssumptionNode(assertions: Set[SimpleAssertionNode], assumptions: Set[SimpleAssumptionNode]) extends AssumptionAnalysisNode {

  override def toString: String =
    assertions.mkString(" && ") + " --> " + assumptions.mkString(" && ")

  override def equals(other: AssumptionAnalysisNode): Boolean = {
    false // TODO ake
  }
}
