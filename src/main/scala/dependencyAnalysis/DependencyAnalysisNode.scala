package viper.silicon.dependencyAnalysis

import viper.silicon.dependencyAnalysis.AssumptionType.AssumptionType
import viper.silicon.interfaces.state.Chunk
import viper.silicon.state.terms.{False, Term, Var}
import viper.silver.ast.Position
import viper.silver.dependencyAnalysis.AbstractDependencyAnalysisNode


trait DependencyAnalysisNode extends AbstractDependencyAnalysisNode {

  /**
   * The unique node id, which is also given to the SMT solver such that unsat cores can be mapped back to dependency nodes.
   */
  val id: Int = DependencyGraphHelper.nextId()

  /**
   * Stores information about which source code statement / expression created this node.
   * This information is crucial to lift lower-level graphs to higher-level graphs and to present user-readable
   * dependency results.
   */
  val sourceInfo: AnalysisSourceInfo

  /**
   * The assumption / assertion type of the node which is heavily used in dependency graph queries to filter nodes,
   * for example, to only present explicit assumptions.
   */
  val assumptionType: AssumptionType

  /**
   * A flag that, when set to true, indicates that the node should not receive any additional edges, unless explicitly added.
   * This is useful to increase precision of the dependency analysis, for example, to ensure that an assumption does not
   * depend on more assertions than necessary.
   */
  val isClosed: Boolean

  /**
   * The assumes or asserted Silicon term. Currently, only used for debugging purposes.
   */
  val term: Term
  def getTerm: Term = term

  def getUserLevelRepresentation: String = sourceInfo.getTopLevelSource.toString
  def getSourceCodePosition: Position = sourceInfo.getTopLevelSource.getPosition

  /*
    Some string representations, mainly used for debugging purposes.
    The strings represented to users are obtained via sourceInfo.toString and do not contain any low-level information
    about the node (such as the id or term).
   */
  override def toString: String = id.toString + " | " + getNodeString + " | " + sourceInfo.toString
  def getNodeString: String
  def getNodeType: String

  override def hashCode(): Int =
    toString.hashCode
}

trait GeneralAssumptionNode extends DependencyAnalysisNode {
  override def getNodeType: String = "Assumption"
}
trait GeneralAssertionNode extends DependencyAnalysisNode {
  override def getNodeType: String = "Assertion"

  val hasFailed: Boolean

  def getAssertFailedNode(): GeneralAssertionNode
}

trait ChunkAnalysisInfo {
  val chunk: Chunk
  def getChunk: Chunk = chunk
}

case class SimpleAssumptionNode(term: Term, description: Option[String], sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType, isClosed: Boolean) extends GeneralAssumptionNode {
  override def getNodeString: String = "assume " + term.toString + description.map(" (" + _ + ")").getOrElse("")
}

case class AxiomAssumptionNode(term: Term, description: Option[String], sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType, isClosed: Boolean) extends GeneralAssumptionNode {
  override def getNodeString: String = "assume axiom " + term.toString + description.map(" (" + _ + ")").getOrElse("")
}

case class SimpleAssertionNode(term: Term, assumptionType: AssumptionType, sourceInfo: AnalysisSourceInfo, isClosed: Boolean, hasFailed: Boolean = false) extends GeneralAssertionNode {
  override def getNodeString: String = "assert " + term.toString

  override def getAssertFailedNode(): GeneralAssertionNode = SimpleAssertionNode(term, assumptionType, sourceInfo, isClosed, hasFailed=true)
}

case class SimpleCheckNode(term: Term, assumptionType: AssumptionType, sourceInfo: AnalysisSourceInfo, isClosed: Boolean, hasFailed: Boolean = false) extends GeneralAssertionNode {
  override def getNodeString: String = "check " + term
  override def getNodeType: String = "Check"

  override def getAssertFailedNode(): GeneralAssertionNode = SimpleCheckNode(term, assumptionType, sourceInfo, isClosed, hasFailed=true)
}

case class PermissionInhaleNode(chunk: Chunk, term: Term, sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType, isClosed: Boolean, labelNode: LabelNode) extends GeneralAssumptionNode with ChunkAnalysisInfo {
  override def getNodeString: String = "inhale " + chunk.toString
  override def getNodeType: String = "Inhale"
}

case class PermissionExhaleNode(chunk: Chunk, term: Term, sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType, isClosed: Boolean, hasFailed: Boolean = false) extends GeneralAssertionNode with ChunkAnalysisInfo {
  override def getNodeType: String = "Exhale"
  override def getNodeString: String = "exhale " + chunk.toString

  override def getAssertFailedNode(): GeneralAssertionNode = PermissionExhaleNode(chunk, term, sourceInfo, assumptionType, isClosed, hasFailed=true)
}

/**
 * Label nodes are internally used nodes, mostly used to improve precision of the dependency analysis.
 * They are completely hidden from users.
 */
case class LabelNode(term: Var) extends GeneralAssumptionNode {
  val sourceInfo: AnalysisSourceInfo = NoAnalysisSourceInfo()
  val assumptionType: AssumptionType = AssumptionType.Internal
  val isClosed: Boolean = true
  val description: String = term.toString
  override def getNodeType: String = "Label"
  override def getNodeString: String = "assume " + description
}

/**
 * Represents the fact that a branch has been found to be infeasible.
 * Infeasibility nodes should always depend on the proof of false and all subsequent assertions on the infeasible path
 * should depend on the infeasibility node.
 * Infeasibility nodes allow to distinguish between dependencies coming from the fact that the assertion is not reachable
 * on a given path and dependencies used to prove the assertion on feasible paths.
 */
case class InfeasibilityNode(sourceInfo: AnalysisSourceInfo) extends GeneralAssumptionNode {
  val term: Term = False
  val assumptionType: AssumptionType = AssumptionType.Implicit // TODO ake: assumption type?
  val isClosed: Boolean = true
  val description: String = "False"

  override def getNodeType: String = "Infeasible"
  override def getNodeString: String = "infeasible"
}
