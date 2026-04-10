package viper.silicon.dependencyAnalysis

import viper.silicon.verifier.Verifier
import viper.silver.ast
import viper.silver.ast._
import viper.silver.dependencyAnalysis._

/**
 * Stores all information about the currently evaluated statement/expression such that the dependency analysis can
 * correctly add nodes and edges to the graph.
 */
case class DependencyAnalysisInfos(sourceInfos: List[AnalysisSourceInfo], dependencyTypes: List[DependencyTypeInfo], mergeInfos: List[DependencyAnalysisMergeInfo], joinInfos: List[DependencyAnalysisJoinInfo], nodes: List[ast.Node]) {

  def addInfo(info: ast.Info, node: ast.Node): DependencyAnalysisInfos = {
		if(!Verifier.config.enableDependencyAnalysis()) return this

    val newSourceInfos = sourceInfos ++ info.getUniqueInfo[AnalysisSourceInfo].toList
    val newDependencyInfos = dependencyTypes ++ info.getUniqueInfo[DependencyTypeInfo].toList
    val newMergeInfos = mergeInfos ++ info.getUniqueInfo[DependencyAnalysisMergeInfo].toList
    val newJoinInfos = joinInfos ++ info.getUniqueInfo[DependencyAnalysisJoinInfo].toList
    DependencyAnalysisInfos(newSourceInfos, newDependencyInfos, newMergeInfos, newJoinInfos, nodes ++ List(node))
  }

  def addInfo(info: ast.Info): DependencyAnalysisInfos = {
		if(!Verifier.config.enableDependencyAnalysis()) return this

    val newSourceInfos = sourceInfos ++ info.getUniqueInfo[AnalysisSourceInfo].toList
    val newDependencyInfos = dependencyTypes ++ info.getUniqueInfo[DependencyTypeInfo].toList
    val newMergeInfos = mergeInfos ++ info.getUniqueInfo[DependencyAnalysisMergeInfo].toList
    val newJoinInfos = joinInfos ++ info.getUniqueInfo[DependencyAnalysisJoinInfo].toList
    DependencyAnalysisInfos(newSourceInfos, newDependencyInfos, newMergeInfos, newJoinInfos, nodes)
  }

  def addInfo(infoString: String, pos: ast.Position, dependencyType: DependencyType): DependencyAnalysisInfos = {
		if(!Verifier.config.enableDependencyAnalysis()) return this
		this.copy(sourceInfos = sourceInfos ++ List(StringAnalysisSourceInfo(infoString, pos)), dependencyTypes = dependencyTypes ++ List(DependencyTypeInfo(dependencyType)))
	}

	def withDependencyType(dependencyType: DependencyType): DependencyAnalysisInfos = {
		if(!Verifier.config.enableDependencyAnalysis()) return this

		this.copy(dependencyTypes = DependencyTypeInfo(dependencyType) +: dependencyTypes)
  }

  def withSource(source: AnalysisSourceInfo): DependencyAnalysisInfos = {
		if(!Verifier.config.enableDependencyAnalysis()) return this

		this.copy(sourceInfos = source +: sourceInfos)
  }

  def getSourceInfo: AnalysisSourceInfo =
		sourceInfos.headOption.getOrElse(nodes.headOption.map(AnalysisSourceInfo.createAnalysisSourceInfo).getOrElse(StringAnalysisSourceInfo("Unknown", NoPosition)))

  def getDependencyType: DependencyType =
		dependencyTypes.headOption.map(_.dependencyType).getOrElse(DependencyType.make(AssumptionType.Unknown))

  def getMergeInfo: DependencyAnalysisMergeInfo = mergeInfos.headOption.getOrElse(SimpleDependencyAnalysisMerge(getSourceInfo))

  def getJoinInfo: List[SimpleDependencyAnalysisJoin] = {
    joinInfos.map {
			case EvalStackDependencyAnalysisJoin(joinType, edgeType) => SimpleDependencyAnalysisJoin(sourceInfos.last, joinType, edgeType)
			case a: SimpleDependencyAnalysisJoin => a
		}
  }

  def withMergeInfo(mergeInfo: DependencyAnalysisMergeInfo): DependencyAnalysisInfos = {
		if(!Verifier.config.enableDependencyAnalysis()) return this

		this.copy(mergeInfos = mergeInfo +: mergeInfos)
	}

	def withJoinInfo(joinInfo: DependencyAnalysisJoinInfo): DependencyAnalysisInfos = {
		if(!Verifier.config.enableDependencyAnalysis()) return this

		this.copy(joinInfos = joinInfo +: joinInfos)
	}
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

	def createUnique(infoString: String, dependencyType: DependencyType): DependencyAnalysisInfos =
		create(StringAnalysisSourceInfo(s"$infoString-${DependencyGraphHelper.nextId()}", NoPosition), dependencyType)
}




class CustomDependencyAnalysisNode(description: String, sourceInfoOpt: Option[AnalysisSourceInfo], dependencyTypeOpt: Option[DependencyType],
                                   createAssertionNode: Boolean, createAssumptionNode: Boolean,
                                   mergeInfoOpt: Option[DependencyAnalysisMergeInfo], joinInfoOpt: Option[DependencyAnalysisJoinInfo])