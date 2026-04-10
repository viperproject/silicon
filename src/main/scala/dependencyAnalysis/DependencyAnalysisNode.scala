package viper.silicon.dependencyAnalysis

import viper.silicon.interfaces.state.Chunk
import viper.silicon.state.terms.{False, Term, Var}
import viper.silver.ast.{DependencyAnalysisMergeInfo, NoDependencyAnalysisMerge, Position, SimpleDependencyAnalysisJoin}
import viper.silver.dependencyAnalysis.AssumptionType.AssumptionType
import viper.silver.dependencyAnalysis.{AnalysisSourceInfo, AssumptionType, NoAnalysisSourceInfo}


trait DependencyAnalysisNode {

  /**
   * The unique node id, which is also given to the SMT solver such that unsat cores can be mapped back to dependency nodes.
   */
  val _id: Option[Int]
  val id: Int = if(_id.isEmpty) DependencyGraphHelper.nextId() else _id.get


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
	 * The merge info determines which nodes should be "merged" when lifting the graph to the user level. In reality,
	 * the nodes are connected by edges instead and are only partially merged.
	 */
  val mergeInfo: DependencyAnalysisMergeInfo

	/**
	 * The join infos specify how the node should be joined with nodes of other verification component's graphs.
	 */
  val joinInfos: List[SimpleDependencyAnalysisJoin]

  /**
   * The assumes or asserted Silicon term. Currently, only used for debugging purposes.
   */
  val term: Term
  def getTerm: Term = term

  def getUserLevelRepresentation: String = sourceInfo.toString
  def getSourceCodePosition: Position = sourceInfo.getPosition

  /**
    Some string representations, mainly used for debugging purposes.
    The strings represented to users are obtained via sourceInfo.toString and do not contain any low-level information
    about the node (such as the id or term).
   */
  override def toString: String = id.toString + " | " + getNodeString + " | " + sourceInfo.toString
  def getNodeString: String
  def getNodeType: String

  // TODO ake: remove workaround
  override def hashCode(): Int =
    id.hashCode()

  // TODO ake: remove workaround
  override def equals(obj: Any): Boolean = obj match {
    case node: DependencyAnalysisNode => node.id == this.id
    case _ => false
  }
}

trait GeneralAssumptionNode extends DependencyAnalysisNode {
  override def getNodeType: String = "Assumption"

}
trait GeneralAssertionNode extends DependencyAnalysisNode {
  override def getNodeType: String = "Assertion"

  val hasFailed: Boolean

  def getAssertFailedNode: GeneralAssertionNode
}

// this is not strictly needed anymore but storing the chunk and label node is useful for debugging purposes
trait ChunkAnalysisInfo {
  val chunk: Chunk
  val labelNode: LabelNode
}

case class SimpleAssumptionNode(term: Term, description: Option[String], sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType, mergeInfo: DependencyAnalysisMergeInfo, joinInfos: List[SimpleDependencyAnalysisJoin], _id: Option[Int]=None) extends GeneralAssumptionNode {
  override def getNodeString: String = "assume " + term.toString + description.map(" (" + _ + ")").getOrElse("")
}

case class AxiomAssumptionNode(term: Term, description: Option[String], sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType, mergeInfo: DependencyAnalysisMergeInfo, joinInfos: List[SimpleDependencyAnalysisJoin], _id: Option[Int]=None) extends GeneralAssumptionNode {
  override def getNodeString: String = "assume axiom " + term.toString + description.map(" (" + _ + ")").getOrElse("")
  override def getNodeType: String = "Axiom"
}

case class SimpleAssertionNode(term: Term, sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType, mergeInfo: DependencyAnalysisMergeInfo, joinInfos: List[SimpleDependencyAnalysisJoin], hasFailed: Boolean = false, _id: Option[Int]=None) extends GeneralAssertionNode {
  override def getNodeString: String = "assert " + term.toString

  override def getAssertFailedNode: GeneralAssertionNode = SimpleAssertionNode(term, sourceInfo, assumptionType, mergeInfo, hasFailed=true, joinInfos=joinInfos)
}

case class SimpleCheckNode(term: Term, sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType, mergeInfo: DependencyAnalysisMergeInfo, joinInfos: List[SimpleDependencyAnalysisJoin], hasFailed: Boolean = false, _id: Option[Int]=None) extends GeneralAssertionNode {
  override def getNodeString: String = "check " + term
  override def getNodeType: String = "Check"

  override def getAssertFailedNode: GeneralAssertionNode = SimpleCheckNode(term, sourceInfo, assumptionType, mergeInfo, joinInfos, hasFailed=true)
}

case class PermissionInhaleNode(chunk: Chunk, term: Term, sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType, mergeInfo: DependencyAnalysisMergeInfo, labelNode: LabelNode, joinInfos: List[SimpleDependencyAnalysisJoin], _id: Option[Int]=None) extends GeneralAssumptionNode with ChunkAnalysisInfo {
  override def getNodeString: String = "inhale " + chunk.toString
  override def getNodeType: String = "Inhale"
}

case class PermissionExhaleNode(chunk: Chunk, term: Term, sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType, mergeInfo: DependencyAnalysisMergeInfo, labelNode: LabelNode, joinInfos: List[SimpleDependencyAnalysisJoin], hasFailed: Boolean = false, _id: Option[Int]=None) extends GeneralAssertionNode with ChunkAnalysisInfo {
  override def getNodeType: String = "Exhale"
  override def getNodeString: String = "exhale " + chunk.toString

  override def getAssertFailedNode: GeneralAssertionNode = PermissionExhaleNode(chunk, term, sourceInfo, assumptionType, mergeInfo, labelNode, joinInfos, hasFailed=true, _id=_id)
}

/**
 * Label nodes are internally-used nodes, mostly used to improve precision of the dependency analysis.
 * They are completely hidden from users.
 */
case class LabelNode(term: Var, _id: Option[Int]=None) extends GeneralAssumptionNode {
  val sourceInfo: AnalysisSourceInfo = NoAnalysisSourceInfo()
  val assumptionType: AssumptionType = AssumptionType.Internal
  val mergeInfo: DependencyAnalysisMergeInfo = NoDependencyAnalysisMerge()
  val description: String = term.toString
  val joinInfos: List[SimpleDependencyAnalysisJoin] = List.empty
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
case class InfeasibilityNode(sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType, _id: Option[Int]=None) extends GeneralAssumptionNode {
  val term: Term = False
  val mergeInfo: DependencyAnalysisMergeInfo = NoDependencyAnalysisMerge()
  val description: String = "False"
  val joinInfos: List[SimpleDependencyAnalysisJoin] = List.empty

  override def getNodeType: String = "Infeasible"
  override def getNodeString: String = "infeasible"
}
