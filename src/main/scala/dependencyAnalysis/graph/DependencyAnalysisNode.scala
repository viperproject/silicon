// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silicon.dependencyAnalysis.graph

import viper.silicon.dependencyAnalysis.AnalysisInfos
import viper.silicon.state.chunks.Chunk
import viper.silicon.state.terms.{False, Term, Var}
import viper.silver.dependencyAnalysis.AssumptionType.AssumptionType
import viper.silver.dependencyAnalysis._


/**
 * The information shared by all nodes that describes where a node comes from.
 *
 * @param sourceInfo    Stores information about which source code statement / expression created this node.
 *                      This information is crucial to lift lower-level graphs to higher-level graphs and to present
 *                      user-readable dependency results.
 * @param originType    The assumption / assertion type of the node which is heavily used in dependency graph queries
 *                      to filter nodes, for example, to only present explicit assumptions.
 * @param mergeInfo     The merge info determines which nodes should be "merged" when lifting the graph to the user level.
 *                      In reality, the nodes are connected by edges instead and are only partially merged.
 * @param joinInfos     The join infos specify how the node should be joined with nodes of other verification component's graphs.
 * @param memberStr     The program member (method, function) that the node belongs to
 */
case class NodeMetadata(sourceInfo: DependencyAnalysisSourceInfo, originType: AssumptionType, mergeInfo: DependencyAnalysisMergeInfo,
                        joinInfos: List[SimpleDependencyAnalysisJoin], memberStr: String)

object NodeMetadata {
  def forAssumption(analysisInfos: AnalysisInfos, memberStr: String): NodeMetadata =
    NodeMetadata(analysisInfos.getSourceInfo, analysisInfos.getDependencyType.assumptionType, analysisInfos.getMergeInfo,
      analysisInfos.getJoinInfo.filterNot(_.assertOnly), memberStr)

  def forAssertion(analysisInfos: AnalysisInfos, memberStr: String): NodeMetadata =
    NodeMetadata(analysisInfos.getSourceInfo, analysisInfos.getDependencyType.assertionType, analysisInfos.getMergeInfo,
      analysisInfos.getJoinInfo, memberStr)
}

sealed trait DependencyAnalysisNode {

  /**
   * The unique node id, which is also given to the SMT solver such that unsat cores can be mapped back to dependency nodes.
   */
  val id: Int

  val metadata: NodeMetadata

  def sourceInfo: DependencyAnalysisSourceInfo = metadata.sourceInfo
  def originType: AssumptionType = metadata.originType
  def mergeInfo: DependencyAnalysisMergeInfo = metadata.mergeInfo
  def joinInfos: List[SimpleDependencyAnalysisJoin] = metadata.joinInfos
  def memberStr: String = metadata.memberStr

  /**
   * The assumes or asserted Silicon term. Currently, only used for debugging purposes.
   */
  val term: Term

  def getUserLevelRepresentation: String = sourceInfo.toString

  /**
    Some string representations, mainly used for debugging purposes.
    The strings represented to users are obtained via sourceInfo.toString and do not contain any low-level information
    about the node (such as the id or term).
   */
  override def toString: String = id.toString + " | " + getNodeString + " | " + sourceInfo.toString
  def getNodeString: String

  /**
   * The tag identifying the type of this node in exported graphs.
   */
  def getNodeType: String
}

sealed trait GeneralAssumptionNode extends DependencyAnalysisNode {
  override def getNodeType: String = "Assumption"

}

sealed trait GeneralAssertionNode extends DependencyAnalysisNode {
  override def getNodeType: String = "Assertion"

  val hasFailed: Boolean

  /**
   * @return a copy of the current node (including the id!) but with hasFailed set to true.
   */
  def getAssertFailedNode: GeneralAssertionNode
}

// this is not strictly needed anymore but storing the chunk and label node is useful for debugging purposes
trait ChunkAnalysisInfo {
  val chunk: Chunk
  val labelNode: LabelNode
}

case class SimpleAssumptionNode private[graph] (override val id: Int, override val term: Term, description: Option[String],
                                                override val metadata: NodeMetadata) extends GeneralAssumptionNode {
  override def getNodeString: String = "assume " + term.toString + description.map(" (" + _ + ")").getOrElse("")
}

case class AxiomAssumptionNode private[graph] (override val id: Int, override val term: Term, description: Option[String],
                                               override val metadata: NodeMetadata) extends GeneralAssumptionNode {
  override def getNodeString: String = "assume axiom " + term.toString + description.map(" (" + _ + ")").getOrElse("")
  override def getNodeType: String = "Axiom"
}

case class SimpleAssertionNode private[graph] (override val id: Int, override val term: Term, override val metadata: NodeMetadata,
                                               override val hasFailed: Boolean = false) extends GeneralAssertionNode {
  override def getNodeString: String = "assert " + term.toString

  override def getAssertFailedNode: GeneralAssertionNode = copy(hasFailed = true)
}

case class SimpleCheckNode private[graph] (override val id: Int, override val term: Term, override val metadata: NodeMetadata,
                                           override val hasFailed: Boolean = false) extends GeneralAssertionNode {
  override def getNodeString: String = "check " + term
  override def getNodeType: String = "Check"

  override def getAssertFailedNode: GeneralAssertionNode = copy(hasFailed = true)
}

case class PermissionInhaleNode private[graph] (override val id: Int, override val chunk: Chunk, override val term: Term,
                                                override val metadata: NodeMetadata, override val labelNode: LabelNode
                                               ) extends GeneralAssumptionNode with ChunkAnalysisInfo {
  override def getNodeString: String = "inhale " + chunk.toString
  override def getNodeType: String = "Inhale"
}

case class PermissionExhaleNode private[graph] (override val id: Int, override val chunk: Chunk, override val term: Term,
                                                override val metadata: NodeMetadata, override val labelNode: LabelNode,
                                                override val hasFailed: Boolean = false
                                               ) extends GeneralAssertionNode with ChunkAnalysisInfo {
  override def getNodeType: String = "Exhale"
  override def getNodeString: String = "exhale " + chunk.toString

  override def getAssertFailedNode: GeneralAssertionNode = copy(hasFailed = true)
}

/**
 * Label nodes are nodes used internally, mostly used to improve precision of the dependency analysis.
 * By default, they get removed from the final graph. When debugging the DA is enabled, they are kept but still marked internal.
 */
case class LabelNode private[graph] (override val id: Int, override val term: Var, labelMemberStr: String) extends GeneralAssumptionNode {
  override val metadata: NodeMetadata =
    NodeMetadata(new NoDependencyAnalysisSourceInfo(), AssumptionType.Internal, NoDependencyAnalysisMerge(), List.empty, labelMemberStr)
  val description: String = term.toString
  override def getNodeType: String = "Label"
  override def getNodeString: String = "assume " + description
}

/**
 * Represents the fact that a branch has been found to be infeasible allowing us to distinguish between dependencies
 * coming from the fact that the assertion is not reachable on a given path and dependencies used to prove the
 * assertion on feasible paths.
 *
 * Infeasibility nodes should always depend on the proof of false.
 * All subsequent assertions on the infeasible path should depend on the infeasibility node.
 */
case class InfeasibilityNode private[graph] (override val id: Int, infeasibleSourceInfo: DependencyAnalysisSourceInfo,
                                             infeasibleOriginType: AssumptionType, infeasibleMemberStr: String) extends GeneralAssumptionNode {
  override val term: Term = False
  override val metadata: NodeMetadata =
    NodeMetadata(infeasibleSourceInfo, infeasibleOriginType, NoDependencyAnalysisMerge(), List.empty, infeasibleMemberStr)
  val description: String = "False"

  override def getNodeType: String = "Infeasible"
  override def getNodeString: String = "infeasible"
}

object DependencyNodeFactory {

  def createSimpleAssumptionNode(term: Term, description: Option[String], metadata: NodeMetadata): SimpleAssumptionNode =
    SimpleAssumptionNode(DependencyGraphHelper.nextId(), term, description, metadata)

  def createAxiomAssumptionNode(term: Term, description: Option[String], metadata: NodeMetadata): AxiomAssumptionNode =
    AxiomAssumptionNode(DependencyGraphHelper.nextId(), term, description, metadata)

  def createSimpleAssertionNode(term: Term, metadata: NodeMetadata, hasFailed: Boolean = false): SimpleAssertionNode =
    SimpleAssertionNode(DependencyGraphHelper.nextId(), term, metadata, hasFailed)

  def createSimpleCheckNode(term: Term, metadata: NodeMetadata, hasFailed: Boolean = false): SimpleCheckNode =
    SimpleCheckNode(DependencyGraphHelper.nextId(), term, metadata, hasFailed)

  def createPermissionInhaleNode(chunk: Chunk, term: Term, metadata: NodeMetadata, labelNode: LabelNode): PermissionInhaleNode =
    PermissionInhaleNode(DependencyGraphHelper.nextId(), chunk, term, metadata, labelNode)

  def createPermissionExhaleNode(chunk: Chunk, term: Term, metadata: NodeMetadata, labelNode: LabelNode, hasFailed: Boolean = false): PermissionExhaleNode =
    PermissionExhaleNode(DependencyGraphHelper.nextId(), chunk, term, metadata, labelNode, hasFailed)

  def createLabelNode(term: Var, memberStr: String): LabelNode =
    LabelNode(DependencyGraphHelper.nextId(), term, memberStr)

  def createInfeasibilityNode(sourceInfo: DependencyAnalysisSourceInfo, originType: AssumptionType, memberStr: String): InfeasibilityNode =
    InfeasibilityNode(DependencyGraphHelper.nextId(), sourceInfo, originType, memberStr)
}
