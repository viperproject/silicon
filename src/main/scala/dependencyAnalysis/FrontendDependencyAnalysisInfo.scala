package viper.silicon.dependencyAnalysis

import viper.silicon.dependencyAnalysis.AssumptionType.AssumptionType
import viper.silicon.state.terms.True
import viper.silver.ast.{Info, Position}

abstract class FrontendDependencyAnalysisInfo extends Info {
  override val comment = Nil
  override val isCached = false

  val info: String
  val pos: Position
  val dependencyType: Option[DependencyType]=None

  def getAnalysisSourceInfo: AnalysisSourceInfo
}

case class SimpleFrontendDependencyAnalysisInfo(sourceInfo: AnalysisSourceInfo, _dependencyType: DependencyType) extends FrontendDependencyAnalysisInfo {

  override val info: String = sourceInfo.toString
  override val pos: Position = sourceInfo.getPosition
  override val dependencyType: Option[DependencyType] = Some(_dependencyType)

  override def getAnalysisSourceInfo: AnalysisSourceInfo = sourceInfo
}

/*
 Viper statements / expressions with a DependencyAnalysisJoinNodeInfo will produce an assertion and assumption node with the given source info and dependency type,
 and with isJoinNode set to true.
 The idea is that these nodes can be used to join graphs without the need for an explicit method call.
 We use this, for example, for Gobra interfaces and implementation proofs.
 */
case class DependencyAnalysisJoinNodeInfo(sourceInfo: AnalysisSourceInfo, _dependencyType: DependencyType) extends FrontendDependencyAnalysisInfo {
  def getAssertionNode: GeneralAssertionNode =
    SimpleAssertionNode(True, sourceInfo, AssumptionType.CustomInternal, isClosed=false, isJoinNode=true)

  def getAssertionNode(outerSourceInfo: AnalysisSourceInfo): GeneralAssertionNode =
    SimpleAssertionNode(True, CompositeAnalysisSourceInfo(outerSourceInfo, sourceInfo), AssumptionType.CustomInternal,  isClosed=false, isJoinNode=true)

  def getAssertionNode(outerSourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType): GeneralAssertionNode =
    SimpleAssertionNode(True, CompositeAnalysisSourceInfo(outerSourceInfo, sourceInfo), assumptionType,  isClosed=false, isJoinNode=true)

  def getAssumptionNode(outerSourceInfo: AnalysisSourceInfo): GeneralAssumptionNode =
    SimpleAssumptionNode(True, None, CompositeAnalysisSourceInfo(outerSourceInfo, sourceInfo), AssumptionType.CustomInternal, isClosed=false, isJoinNode=true)

  override val info: String = sourceInfo.toString
  override val pos: Position = sourceInfo.getPosition
  override val dependencyType: Option[DependencyType] = Some(_dependencyType)

  override def getAnalysisSourceInfo: AnalysisSourceInfo = sourceInfo
}