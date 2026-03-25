package viper.silicon.dependencyAnalysis

import jdk.jshell.spi.ExecutionControl.NotImplementedException
import viper.silicon.dependencyAnalysis.JoinType.JoinType
import viper.silver.ast

trait DependencyAnalysisInfo {
  def getSourceInfo: AnalysisSourceInfo
  def getDependencyType: DependencyType
  def getMergeInfo: DependencyAnalysisMergeInfo
  def getJoinInfo: DependencyAnalysisJoinInfo

  def withDependencyType(newDependencyType: DependencyType): DependencyAnalysisInfo

  def withSource(sourceInfo: AnalysisSourceInfo): DependencyAnalysisInfo

  def withAdditionalEvalNode(analysisSourceInfo: AnalysisSourceInfo): DependencyAnalysisInfo
}


case class NoDependencyAnalysisInfo() extends DependencyAnalysisInfo {
  override def getSourceInfo: AnalysisSourceInfo = throw new NotImplementedException("NoDependencyAnalysisInfo.getSourceInfo")

  override def getDependencyType: DependencyType = throw new NotImplementedException("NoDependencyAnalysisInfo.getDependencyType")

  override def getMergeInfo: DependencyAnalysisMergeInfo = throw new NotImplementedException("NoDependencyAnalysisInfo.getMergeInfo")

  override def getJoinInfo: DependencyAnalysisJoinInfo = throw new NotImplementedException("NoDependencyAnalysisInfo.getJoinInfo")

  override def withDependencyType(newDependencyType: DependencyType): NoDependencyAnalysisInfo = this

  override def withSource(sourceInfo: AnalysisSourceInfo): DependencyAnalysisInfo = this

  override def withAdditionalEvalNode(analysisSourceInfo: AnalysisSourceInfo): NoDependencyAnalysisInfo = this
}

case class DependencyAnalysisInfoWithoutSource( dependencyType: DependencyType,
                                                mergeInfo: Option[DependencyAnalysisMergeInfo]=None,
                                               joinInfo: DependencyAnalysisJoinInfo=NoDependencyAnalysisJoin(),
                                               // additionalNodes: Set[CustomDependencyAnalysisNode]=Set.empty
                                               ) extends DependencyAnalysisInfo {

  override def getSourceInfo: AnalysisSourceInfo = throw new NotImplementedException("NoDependencyAnalysisInfo.getSourceInfo")

  override def getDependencyType: DependencyType = dependencyType

  override def getMergeInfo: DependencyAnalysisMergeInfo = mergeInfo.get

  override def getJoinInfo: DependencyAnalysisJoinInfo = joinInfo

  override def withDependencyType(newDependencyType: DependencyType): DependencyAnalysisInfoWithoutSource =
    this.copy(dependencyType = newDependencyType)

  def withIsJoinNode(newJoinInfo: DependencyAnalysisJoinInfo): DependencyAnalysisInfoWithoutSource =
    this.copy(joinInfo = newJoinInfo)

  override def withAdditionalEvalNode(analysisSourceInfo: AnalysisSourceInfo): FullDependencyAnalysisInfo =
    FullDependencyAnalysisInfo(analysisSourceInfo, List(analysisSourceInfo), dependencyType, mergeInfo.getOrElse(SimpleDependencyAnalysisMerge(analysisSourceInfo)), joinInfo)

  override def withSource(sourceInfo: AnalysisSourceInfo): DependencyAnalysisInfo = withAdditionalEvalNode(sourceInfo)

}



case class FullDependencyAnalysisInfo(sourceInfo: AnalysisSourceInfo,
                                      evaluationStack: List[AnalysisSourceInfo], /* TODO ake: do we need this? */
                                      dependencyType: DependencyType,
                                      mergeInfo: DependencyAnalysisMergeInfo, /* required for lifting the low-level graph */
                                      joinInfo: DependencyAnalysisJoinInfo=NoDependencyAnalysisJoin(), /* required for interprocedural edges */
                                      //additionalNodes: Set[CustomDependencyAnalysisNode]=Set.empty, /* TODO ake: should be part of the AST node info but does not need to be propagated */
                                     ) extends DependencyAnalysisInfo {

  override def getSourceInfo: AnalysisSourceInfo = sourceInfo

  override def getDependencyType: DependencyType = dependencyType

  override def getMergeInfo: DependencyAnalysisMergeInfo = mergeInfo

  override def getJoinInfo: DependencyAnalysisJoinInfo = joinInfo

  override def withAdditionalEvalNode(analysisSourceInfo: AnalysisSourceInfo): FullDependencyAnalysisInfo =
    this.copy(evaluationStack=analysisSourceInfo+:evaluationStack)
  override def withDependencyType(newDependencyType: DependencyType): FullDependencyAnalysisInfo =
    this.copy(dependencyType=newDependencyType)
  def withMergeInfo(newMergeInfo: DependencyAnalysisMergeInfo): FullDependencyAnalysisInfo =
    this.copy(mergeInfo=newMergeInfo)
  def withJoinInfo(newJoinInfo: DependencyAnalysisJoinInfo): FullDependencyAnalysisInfo =
    this.copy(joinInfo=newJoinInfo)


  override def withSource(sourceInfo: AnalysisSourceInfo): DependencyAnalysisInfo =
    this.copy(sourceInfo=sourceInfo)

}

object FullDependencyAnalysisInfo {
  def create(sourceString: String, dependencyType: DependencyType, mergeInfo: DependencyAnalysisMergeInfo, joinNodeInfo: DependencyAnalysisJoinInfo) = {
    val source = AnalysisSourceInfo.createAnalysisSourceInfo(sourceString, ast.NoPosition)
    FullDependencyAnalysisInfo(source, List(source), dependencyType, mergeInfo, joinNodeInfo)
  }

  def create(exp: ast.Exp) = {
    val source = AnalysisSourceInfo.createAnalysisSourceInfo(exp)
    val dependencyType = DependencyType.Implicit // FIXME ake: extract info from exp and initialize accordingly
    FullDependencyAnalysisInfo(source, List(source), dependencyType, SimpleDependencyAnalysisMerge(source), NoDependencyAnalysisJoin())
  }

  def create(stmt: ast.Stmt) = {
    val source = AnalysisSourceInfo.createAnalysisSourceInfo(stmt)
    val dependencyType = DependencyType.get(stmt) // FIXME ake: extract info from exp and initialize accordingly
    FullDependencyAnalysisInfo(source, List(source), dependencyType, SimpleDependencyAnalysisMerge(source), NoDependencyAnalysisJoin())
  }
}


object JoinType extends Enumeration {
  type JoinType = Value
  val Source, Sink = Value
}

trait DependencyAnalysisJoinInfo {

  def isJoin: Boolean = true

}

case class NoDependencyAnalysisJoin() extends DependencyAnalysisJoinInfo {
  override def isJoin: Boolean = false
}

case class EvalStackDependencyAnalysisJoin(joinType: JoinType) extends DependencyAnalysisJoinInfo

case class SimpleDependencyAnalysisJoin(sourceInfo: AnalysisSourceInfo, joinType: JoinType) extends DependencyAnalysisJoinInfo


trait DependencyAnalysisMergeInfo {

  def isMerge: Boolean = true
}

case class NoDependencyAnalysisMerge() extends DependencyAnalysisMergeInfo {
  override def isMerge: Boolean = false
}

case class SimpleDependencyAnalysisMerge(sourceInfo: AnalysisSourceInfo) extends DependencyAnalysisMergeInfo



class CustomDependencyAnalysisNode(description: String, sourceInfoOpt: Option[AnalysisSourceInfo], dependencyTypeOpt: Option[DependencyType],
                                   createAssertionNode: Boolean, createAssumptionNode: Boolean,
                                   mergeInfoOpt: Option[DependencyAnalysisMergeInfo], joinInfoOpt: Option[DependencyAnalysisJoinInfo])