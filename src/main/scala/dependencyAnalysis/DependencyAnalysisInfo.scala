package viper.silicon.dependencyAnalysis

import viper.silver.ast
import viper.silver.ast.{DependencyAnalysisJoinInfo, DependencyAnalysisMergeInfo, DependencyTypeInfo, EvalStackDependencyAnalysisJoin, NoPosition, SimpleDependencyAnalysisJoin, SimpleDependencyAnalysisMerge}
import viper.silver.dependencyAnalysis.{AnalysisSourceInfo, DependencyType, StringAnalysisSourceInfo}


trait AnalysisInfos {
}

case class DependencyAnalysisInfos(sourceInfos: List[AnalysisSourceInfo], dependencyTypes: List[DependencyTypeInfo], mergeInfos: List[DependencyAnalysisMergeInfo], joinInfos: List[DependencyAnalysisJoinInfo], nodes: List[ast.Node]) extends AnalysisInfos {

  def addInfo(info: ast.Info, node: ast.Node): DependencyAnalysisInfos = {
    val newSourceInfos = sourceInfos ++ info.getUniqueInfo[AnalysisSourceInfo].toList
    val newDependencyInfos = dependencyTypes ++ info.getUniqueInfo[DependencyTypeInfo].toList
    val newMergeInfos = mergeInfos ++ info.getUniqueInfo[DependencyAnalysisMergeInfo].toList
    val newJoinInfos = joinInfos ++ info.getUniqueInfo[DependencyAnalysisJoinInfo].toList
    DependencyAnalysisInfos(newSourceInfos, newDependencyInfos, newMergeInfos, newJoinInfos, nodes ++ List(node))
  }

  def addInfo(info: ast.Info): DependencyAnalysisInfos = {
    val newSourceInfos = sourceInfos ++ info.getUniqueInfo[AnalysisSourceInfo].toList
    val newDependencyInfos = dependencyTypes ++ info.getUniqueInfo[DependencyTypeInfo].toList
    val newMergeInfos = mergeInfos ++ info.getUniqueInfo[DependencyAnalysisMergeInfo].toList
    val newJoinInfos = joinInfos ++ info.getUniqueInfo[DependencyAnalysisJoinInfo].toList
    DependencyAnalysisInfos(newSourceInfos, newDependencyInfos, newMergeInfos, newJoinInfos, nodes)
  }

  def addInfo(infoString: String, pos: ast.Position, dependencyType: DependencyType): DependencyAnalysisInfos =
    this.copy(sourceInfos = sourceInfos ++ List(StringAnalysisSourceInfo(infoString, pos)), dependencyTypes = dependencyTypes ++ List(DependencyTypeInfo(dependencyType)))

  def withDependencyType(dependencyType: DependencyType): DependencyAnalysisInfos = {
    this.copy(dependencyTypes = DependencyTypeInfo(dependencyType) +: dependencyTypes)
  }

  def withSource(source: AnalysisSourceInfo): DependencyAnalysisInfos = {
    this.copy(sourceInfos = source +: sourceInfos)
  }

  def getSourceInfo: AnalysisSourceInfo = sourceInfos.head

  def getDependencyType: DependencyType = dependencyTypes.head.dependencyType

  def getMergeInfo: DependencyAnalysisMergeInfo = mergeInfos.headOption.getOrElse(SimpleDependencyAnalysisMerge(getSourceInfo))

  def getJoinInfo: List[SimpleDependencyAnalysisJoin] = {
    if(joinInfos.isEmpty) return List.empty
    val h = joinInfos.head match {
      case EvalStackDependencyAnalysisJoin(joinType, edgeType) => SimpleDependencyAnalysisJoin(sourceInfos.last, joinType, edgeType)
      case a: SimpleDependencyAnalysisJoin => a
    }
    List(h)
  }

  def withMergeInfo(mergeInfo: DependencyAnalysisMergeInfo): DependencyAnalysisInfos =
    this.copy(mergeInfos = mergeInfo +: mergeInfos)

  def withJoinInfo(joinInfo: DependencyAnalysisJoinInfo): DependencyAnalysisInfos =
    this.copy(joinInfos = joinInfo +: joinInfos)
}

object DependencyAnalysisInfos {
  val DefaultDependencyAnalysisInfos = DependencyAnalysisInfos(List.empty, List.empty, List.empty, List.empty, List.empty)

  def create(sourceInfo: AnalysisSourceInfo, dependencyType: DependencyType, mergeInfo: DependencyAnalysisMergeInfo): DependencyAnalysisInfos =
    DependencyAnalysisInfos(List(sourceInfo), List(DependencyTypeInfo(dependencyType)), List(mergeInfo), List.empty, List.empty)

  def create(sourceInfo: AnalysisSourceInfo, dependencyType: DependencyType): DependencyAnalysisInfos =
    DependencyAnalysisInfos(List(sourceInfo), List(DependencyTypeInfo(dependencyType)), List.empty, List.empty, List.empty)

  def create(infoString: String, dependencyType: DependencyType, mergeInfo: DependencyAnalysisMergeInfo): DependencyAnalysisInfos =
    create(StringAnalysisSourceInfo(infoString, NoPosition), dependencyType, mergeInfo)

  def create(infoString: String, dependencyType: DependencyType): DependencyAnalysisInfos =
    create(StringAnalysisSourceInfo(infoString, NoPosition), dependencyType)
}








class CustomDependencyAnalysisNode(description: String, sourceInfoOpt: Option[AnalysisSourceInfo], dependencyTypeOpt: Option[DependencyType],
                                   createAssertionNode: Boolean, createAssumptionNode: Boolean,
                                   mergeInfoOpt: Option[DependencyAnalysisMergeInfo], joinInfoOpt: Option[DependencyAnalysisJoinInfo])