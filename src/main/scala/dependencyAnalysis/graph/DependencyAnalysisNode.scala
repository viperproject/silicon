// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silicon.dependencyAnalysis.graph

import viper.silicon.state.chunks.Chunk
import viper.silicon.state.terms.{False, Term, Var}
import viper.silver.dependencyAnalysis.AssumptionType.AssumptionType
import viper.silver.dependencyAnalysis._


trait DependencyAnalysisNode {

  /**
   * The unique node id, which is also given to the SMT solver such that unsat cores can be mapped back to dependency nodes.
   */
  val id: Int


  /**
   * Stores information about which source code statement / expression created this node.
   * This information is crucial to lift lower-level graphs to higher-level graphs and to present user-readable
   * dependency results.
   */
  val sourceInfo: DependencyAnalysisSourceInfo

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
   * The program member (method, function) that the node belongs to
   */
  val memberStr: String

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
  def getNodeType: String
}

trait GeneralAssumptionNode extends DependencyAnalysisNode {
  override def getNodeType: String = "Assumption"

}

trait GeneralAssertionNode extends DependencyAnalysisNode {
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

case class SimpleAssumptionNode private[graph] (override val id: Int, override val term: Term,
                           description: Option[String], override val sourceInfo: DependencyAnalysisSourceInfo,
                           override val assumptionType: AssumptionType, override val mergeInfo: DependencyAnalysisMergeInfo,
                           override val joinInfos: List[SimpleDependencyAnalysisJoin], override val memberStr: String
                          ) extends GeneralAssumptionNode {
  override def getNodeString: String = "assume " + term.toString + description.map(" (" + _ + ")").getOrElse("")
}

case class AxiomAssumptionNode private[graph] (override val id: Int, override val term: Term,
                          description: Option[String], override val sourceInfo: DependencyAnalysisSourceInfo,
                          override val assumptionType: AssumptionType, override val mergeInfo: DependencyAnalysisMergeInfo,
                          override val joinInfos: List[SimpleDependencyAnalysisJoin], override val memberStr: String
                         ) extends GeneralAssumptionNode {
  override def getNodeString: String = "assume axiom " + term.toString + description.map(" (" + _ + ")").getOrElse("")
  override def getNodeType: String = "Axiom"
}

case class SimpleAssertionNode private[graph] (override val id: Int, override val term: Term,
                          override val sourceInfo: DependencyAnalysisSourceInfo, override val assumptionType: AssumptionType,
                          override val mergeInfo: DependencyAnalysisMergeInfo, override val joinInfos: List[SimpleDependencyAnalysisJoin],
                          override val memberStr: String, override val hasFailed: Boolean = false
                         ) extends GeneralAssertionNode {
  override def getNodeString: String = "assert " + term.toString

  override def getAssertFailedNode: GeneralAssertionNode =
    SimpleAssertionNode(id, term, sourceInfo, assumptionType, mergeInfo,
      hasFailed = true, joinInfos = joinInfos, memberStr = memberStr)
}

case class SimpleCheckNode private[graph] (override val id: Int, override val term: Term,
                      override val sourceInfo: DependencyAnalysisSourceInfo, override val assumptionType: AssumptionType,
                      override val mergeInfo: DependencyAnalysisMergeInfo, override val joinInfos: List[SimpleDependencyAnalysisJoin],
                      override val memberStr: String, override val hasFailed: Boolean = false
                     ) extends GeneralAssertionNode {
  override def getNodeString: String = "check " + term
  override def getNodeType: String = "Check"

  override def getAssertFailedNode: GeneralAssertionNode =
    SimpleCheckNode(id, term, sourceInfo, assumptionType, mergeInfo, joinInfos,
      memberStr = memberStr, hasFailed = true)
}

case class PermissionInhaleNode private[graph] (override val id: Int, override val chunk: Chunk,
                           override val term: Term, override val sourceInfo: DependencyAnalysisSourceInfo,
                           override val assumptionType: AssumptionType, override val mergeInfo: DependencyAnalysisMergeInfo,
                           override val labelNode: LabelNode, override val joinInfos: List[SimpleDependencyAnalysisJoin],
                           override val memberStr: String
                          ) extends GeneralAssumptionNode with ChunkAnalysisInfo {
  override def getNodeString: String = "inhale " + chunk.toString
  override def getNodeType: String = "Inhale"
}

case class PermissionExhaleNode private[graph] (override val id: Int, override val chunk: Chunk,
                           override val term: Term, override val sourceInfo: DependencyAnalysisSourceInfo,
                           override val assumptionType: AssumptionType, override val mergeInfo: DependencyAnalysisMergeInfo,
                           override val labelNode: LabelNode, override val joinInfos: List[SimpleDependencyAnalysisJoin],
                           override val memberStr: String, override val hasFailed: Boolean = false
                          ) extends GeneralAssertionNode with ChunkAnalysisInfo {
  override def getNodeType: String = "Exhale"
  override def getNodeString: String = "exhale " + chunk.toString

  override def getAssertFailedNode: GeneralAssertionNode =
    PermissionExhaleNode(id, chunk, term, sourceInfo, assumptionType,
      mergeInfo, labelNode, joinInfos, memberStr, hasFailed = true)
}

/**
 * Label nodes are nodes used internally, mostly used to improve precision of the dependency analysis.
 * By default, they get removed from the final graph. When debugging the DA is enabled, they are kept but still marked internal.
 */
case class LabelNode private[graph] (override val id: Int, override val term: Var, override val memberStr: String) extends GeneralAssumptionNode {
  override val sourceInfo: DependencyAnalysisSourceInfo = NoDependencyAnalysisSourceInfo()
  override val assumptionType: AssumptionType = AssumptionType.Internal
  override val mergeInfo: DependencyAnalysisMergeInfo = NoDependencyAnalysisMerge()
  val description: String = term.toString
  override val joinInfos: List[SimpleDependencyAnalysisJoin] = List.empty
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
case class InfeasibilityNode private[graph] (override val id: Int, override val sourceInfo: DependencyAnalysisSourceInfo,
                        override val assumptionType: AssumptionType, 
                        override val memberStr: String) extends GeneralAssumptionNode {
  override val term: Term = False
  override val mergeInfo: DependencyAnalysisMergeInfo = NoDependencyAnalysisMerge()
  val description: String = "False"
  override val joinInfos: List[SimpleDependencyAnalysisJoin] = List.empty

  override def getNodeType: String = "Infeasible"
  override def getNodeString: String = "infeasible"
}

object DependencyNodeFactory {

  def createSimpleAssumptionNode(term: Term, description: Option[String], sourceInfo: DependencyAnalysisSourceInfo,
                                  assumptionType: AssumptionType, mergeInfo: DependencyAnalysisMergeInfo,
                                  joinInfos: List[SimpleDependencyAnalysisJoin], memberStr: String): SimpleAssumptionNode =
    SimpleAssumptionNode(DependencyGraphHelper.nextId(), term, description, sourceInfo, assumptionType, mergeInfo, joinInfos, memberStr)

  def createAxiomAssumptionNode(term: Term, description: Option[String], sourceInfo: DependencyAnalysisSourceInfo,
                                 assumptionType: AssumptionType, mergeInfo: DependencyAnalysisMergeInfo,
                                 joinInfos: List[SimpleDependencyAnalysisJoin], memberStr: String): AxiomAssumptionNode =
    AxiomAssumptionNode(DependencyGraphHelper.nextId(), term, description, sourceInfo, assumptionType, mergeInfo, joinInfos, memberStr)

  def createSimpleAssertionNode(term: Term, sourceInfo: DependencyAnalysisSourceInfo, assumptionType: AssumptionType,
                                 mergeInfo: DependencyAnalysisMergeInfo, joinInfos: List[SimpleDependencyAnalysisJoin],
                                 memberStr: String, hasFailed: Boolean = false): SimpleAssertionNode =
    SimpleAssertionNode(DependencyGraphHelper.nextId(), term, sourceInfo, assumptionType, mergeInfo, joinInfos, memberStr, hasFailed)

  def createSimpleCheckNode(term: Term, sourceInfo: DependencyAnalysisSourceInfo, assumptionType: AssumptionType,
                             mergeInfo: DependencyAnalysisMergeInfo, joinInfos: List[SimpleDependencyAnalysisJoin],
                             memberStr: String, hasFailed: Boolean = false): SimpleCheckNode =
    SimpleCheckNode(DependencyGraphHelper.nextId(), term, sourceInfo, assumptionType, mergeInfo, joinInfos, memberStr, hasFailed)

  def createPermissionInhaleNode(chunk: Chunk, term: Term, sourceInfo: DependencyAnalysisSourceInfo,
                                  assumptionType: AssumptionType, mergeInfo: DependencyAnalysisMergeInfo,
                                  labelNode: LabelNode, joinInfos: List[SimpleDependencyAnalysisJoin],
                                  memberStr: String): PermissionInhaleNode =
    PermissionInhaleNode(DependencyGraphHelper.nextId(), chunk, term, sourceInfo, assumptionType, mergeInfo, labelNode, joinInfos, memberStr)

  def createPermissionExhaleNode(chunk: Chunk, term: Term, sourceInfo: DependencyAnalysisSourceInfo,
                                  assumptionType: AssumptionType, mergeInfo: DependencyAnalysisMergeInfo,
                                  labelNode: LabelNode, joinInfos: List[SimpleDependencyAnalysisJoin],
                                  memberStr: String, hasFailed: Boolean = false): PermissionExhaleNode =
    PermissionExhaleNode(DependencyGraphHelper.nextId(), chunk, term, sourceInfo, assumptionType, mergeInfo, labelNode, joinInfos, memberStr, hasFailed)

  def createLabelNode(term: Var, memberStr: String): LabelNode =
    LabelNode(DependencyGraphHelper.nextId(), term, memberStr)

  def createInfeasibilityNode(sourceInfo: DependencyAnalysisSourceInfo, assumptionType: AssumptionType, memberStr: String): InfeasibilityNode =
    InfeasibilityNode(DependencyGraphHelper.nextId(), sourceInfo, assumptionType, memberStr)
}
