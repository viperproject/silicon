package viper.silicon.dependencyAnalysis

import viper.silicon.dependencyAnalysis.JoinType.JoinType
import viper.silver.ast
import viper.silver.ast.{DependencyTypeInfo, NoPosition}
import viper.silver.dependencyAnalysis.{AnalysisSourceInfo, DependencyType, StringAnalysisSourceInfo}


trait AnalysisInfoes {
}

case class DependencyAnalysisInfoes(sourceInfoes: List[AnalysisSourceInfo], dependencyTypes: List[DependencyTypeInfo], mergeInfoes: List[DependencyAnalysisMergeInfo], joinInfoes: List[DependencyAnalysisJoinInfo], nodes: List[ast.Node]) extends AnalysisInfoes {

  def addInfo(info: ast.Info, node: ast.Node): DependencyAnalysisInfoes = {
    val newSourceInfoes = sourceInfoes ++ info.getUniqueInfo[AnalysisSourceInfo].toList
    val newDependencyInfoes = dependencyTypes ++ info.getUniqueInfo[DependencyTypeInfo].toList
    val newMergeInfoes = mergeInfoes ++ info.getUniqueInfo[DependencyAnalysisMergeInfo].toList
    val newJoinInfoes = joinInfoes ++ info.getUniqueInfo[DependencyAnalysisJoinInfo].toList
    DependencyAnalysisInfoes(newSourceInfoes, newDependencyInfoes, newMergeInfoes, newJoinInfoes, nodes ++ List(node))
  }

  def addInfo(info: ast.Info): DependencyAnalysisInfoes = {
    val newSourceInfoes = sourceInfoes ++ info.getUniqueInfo[AnalysisSourceInfo].toList
    val newDependencyInfoes = dependencyTypes ++ info.getUniqueInfo[DependencyTypeInfo].toList
    val newMergeInfoes = mergeInfoes ++ info.getUniqueInfo[DependencyAnalysisMergeInfo].toList
    val newJoinInfoes = joinInfoes ++ info.getUniqueInfo[DependencyAnalysisJoinInfo].toList
    DependencyAnalysisInfoes(newSourceInfoes, newDependencyInfoes, newMergeInfoes, newJoinInfoes, nodes)
  }

  def addInfo(infoString: String, pos: ast.Position, dependencyType: DependencyType): DependencyAnalysisInfoes =
    this.copy(sourceInfoes = sourceInfoes ++ List(StringAnalysisSourceInfo(infoString, pos)), dependencyTypes = dependencyTypes ++ List(DependencyTypeInfo(dependencyType)))

  def withDependencyType(dependencyType: DependencyType): DependencyAnalysisInfoes = {
    this.copy(dependencyTypes = DependencyTypeInfo(dependencyType) +: dependencyTypes)
  }

  def withSource(source: AnalysisSourceInfo): DependencyAnalysisInfoes = {
    this.copy(sourceInfoes = source +: sourceInfoes)
  }

  def getSourceInfo: AnalysisSourceInfo = sourceInfoes.head

  def getDependencyType: DependencyType = dependencyTypes.head.dependencyType

  def getMergeInfo: DependencyAnalysisMergeInfo = mergeInfoes.headOption.getOrElse(SimpleDependencyAnalysisMerge(getSourceInfo))

  def getJoinInfo: List[SimpleDependencyAnalysisJoin] = {
    if(joinInfoes.isEmpty) return List.empty
    val h = joinInfoes.head match {
      case EvalStackDependencyAnalysisJoin(joinType) => SimpleDependencyAnalysisJoin(sourceInfoes.last, joinType)
      case a: SimpleDependencyAnalysisJoin => a
    }
    List(h)
  }

  def withMergeInfo(mergeInfo: DependencyAnalysisMergeInfo): DependencyAnalysisInfoes =
    this.copy(mergeInfoes = mergeInfo +: mergeInfoes)

  def withJoinInfo(joinInfo: EvalStackDependencyAnalysisJoin): DependencyAnalysisInfoes =
    this.copy(joinInfoes = joinInfo +: joinInfoes)
}

object DependencyAnalysisInfoes {
  val DefaultDependencyAnalysisInfoes = DependencyAnalysisInfoes(List.empty, List.empty, List.empty, List.empty, List.empty)

  def create(sourceInfo: AnalysisSourceInfo, dependencyType: DependencyType, mergeInfo: DependencyAnalysisMergeInfo): DependencyAnalysisInfoes =
    DependencyAnalysisInfoes(List(sourceInfo), List(DependencyTypeInfo(dependencyType)), List(mergeInfo), List.empty, List.empty)

  def create(sourceInfo: AnalysisSourceInfo, dependencyType: DependencyType): DependencyAnalysisInfoes =
    DependencyAnalysisInfoes(List(sourceInfo), List(DependencyTypeInfo(dependencyType)), List.empty, List.empty, List.empty)

  def create(infoString: String, dependencyType: DependencyType, mergeInfo: DependencyAnalysisMergeInfo): DependencyAnalysisInfoes =
    create(StringAnalysisSourceInfo(infoString, NoPosition), dependencyType, mergeInfo)

  def create(infoString: String, dependencyType: DependencyType): DependencyAnalysisInfoes =
    create(StringAnalysisSourceInfo(infoString, NoPosition), dependencyType)
}




object JoinType extends Enumeration {
  type JoinType = Value
  val Source, Sink = Value
}


trait DependencyAnalysisJoinInfo extends ast.Info {
  override def comment: Seq[String] = Nil
  override def isCached: Boolean = false
}

case class EvalStackDependencyAnalysisJoin(joinType: JoinType) extends DependencyAnalysisJoinInfo

case class SimpleDependencyAnalysisJoin(sourceInfo: AnalysisSourceInfo, joinType: JoinType) extends DependencyAnalysisJoinInfo


trait DependencyAnalysisMergeInfo extends ast.Info {

  def isMerge: Boolean

  override def comment: Seq[String] = Nil
  override def isCached: Boolean = false
}

case class NoDependencyAnalysisMerge() extends DependencyAnalysisMergeInfo {
  override def isMerge: Boolean = false
}

case class SimpleDependencyAnalysisMerge(sourceInfo: AnalysisSourceInfo) extends DependencyAnalysisMergeInfo {
  override def isMerge: Boolean = true
}



class CustomDependencyAnalysisNode(description: String, sourceInfoOpt: Option[AnalysisSourceInfo], dependencyTypeOpt: Option[DependencyType],
                                   createAssertionNode: Boolean, createAssumptionNode: Boolean,
                                   mergeInfoOpt: Option[DependencyAnalysisMergeInfo], joinInfoOpt: Option[DependencyAnalysisJoinInfo])