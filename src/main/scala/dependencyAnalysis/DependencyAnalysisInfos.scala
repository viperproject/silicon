// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silicon.dependencyAnalysis

import viper.silicon.SiliconRunner
import viper.silicon.verifier.Verifier
import viper.silver.ast
import viper.silver.ast._
import viper.silver.dependencyAnalysis.AssumptionType.AssumptionType
import viper.silver.dependencyAnalysis._

/**
 * Stores all information about the currently evaluated statement/expression such that the dependency analysis can
 * correctly add nodes and edges to the graph.
 */
case class DependencyAnalysisInfos(sourceInfos: List[DependencyAnalysisSourceInfo], dependencyTypes: List[DependencyTypeInfo], mergeInfos: List[DependencyAnalysisMergeInfo], joinInfos: List[DependencyAnalysisJoinInfo], nodes: List[ast.Node], analysisEnabled: Boolean = true) {

  private def isAnalysisEnabled = Verifier.config.dependencyAnalysisMode.isDefined && analysisEnabled

  def addInfo(info: ast.Info, node: ast.Node): DependencyAnalysisInfos = {
    if (!isAnalysisEnabled) return this

    val newSourceInfos = sourceInfos ++ info.getUniqueInfo[DependencyAnalysisSourceInfo].toList
    val newDependencyInfos = dependencyTypes ++ info.getUniqueInfo[DependencyTypeInfo].toList
    val newMergeInfos = mergeInfos ++ info.getUniqueInfo[DependencyAnalysisMergeInfo].toList
    val newJoinInfos = joinInfos ++ info.getUniqueInfo[DependencyAnalysisJoinInfo].toList
    this.copy(sourceInfos=newSourceInfos, dependencyTypes=newDependencyInfos, mergeInfos=newMergeInfos, joinInfos=newJoinInfos, nodes=nodes ++ List(node))
  }

  def addInfo(info: ast.Info): DependencyAnalysisInfos = {
    if (!isAnalysisEnabled) return this

    val newSourceInfos = sourceInfos ++ info.getUniqueInfo[DependencyAnalysisSourceInfo].toList
    val newDependencyInfos = dependencyTypes ++ info.getUniqueInfo[DependencyTypeInfo].toList
    val newMergeInfos = mergeInfos ++ info.getUniqueInfo[DependencyAnalysisMergeInfo].toList
    val newJoinInfos = joinInfos ++ info.getUniqueInfo[DependencyAnalysisJoinInfo].toList
    this.copy(sourceInfos=newSourceInfos, dependencyTypes=newDependencyInfos, mergeInfos=newMergeInfos, joinInfos=newJoinInfos)
  }

  def addInfo(infoString: String, pos: ast.Position, dependencyType: DependencyType): DependencyAnalysisInfos = {
    if (!isAnalysisEnabled) return this
    this.copy(sourceInfos = sourceInfos ++ List(StringDependencyAnalysisSourceInfo(infoString, pos)), dependencyTypes = dependencyTypes ++ List(DependencyTypeInfo(dependencyType)))
  }

  def withDependencyType(dependencyType: DependencyType): DependencyAnalysisInfos = {
    if (!isAnalysisEnabled) return this

    this.copy(dependencyTypes = DependencyTypeInfo(dependencyType) +: dependencyTypes)
  }

  def withDependencyType(assumptionType: AssumptionType): DependencyAnalysisInfos = {
    if (!isAnalysisEnabled) return this

    this.copy(dependencyTypes = DependencyTypeInfo(DependencyType(assumptionType)) +: dependencyTypes)
  }

  def withSource(source: DependencyAnalysisSourceInfo): DependencyAnalysisInfos = {
    if (!isAnalysisEnabled) return this

    this.copy(sourceInfos = source +: sourceInfos)
  }

  private def getNodeInfo(n: ast.Node): String = {
    n match {
      case np: Positioned =>
        s"${n.toString()} (${np.pos})"
      case _ =>
        s"${n.toString()} (???)"
    }
  }

  private def getDebugInfo: String = {
    val sourceInfo = sourceInfos.headOption.map("source info: " + _.toString + " ").getOrElse("")
    val nodeInfo = if (nodes.nonEmpty) "nodes: " + nodes.map(getNodeInfo).mkString(", ") else ""
    s"$sourceInfo$nodeInfo"
  }

  def getSourceInfo: DependencyAnalysisSourceInfo = {
    if (!isAnalysisEnabled) return StringDependencyAnalysisSourceInfo("Unknown", NoPosition)
    val sourceInfoOpt = sourceInfos.headOption
    if (sourceInfoOpt.isDefined) {
      sourceInfoOpt.get
    } else {
      SiliconRunner.logger.warn(s"WARN: Missing source info for $getDebugInfo")
      nodes.headOption.map(DependencyAnalysisSourceInfo.createAnalysisSourceInfo).getOrElse(StringDependencyAnalysisSourceInfo("Unknown", NoPosition))
    }
  }

  def getDependencyType: DependencyType = {
    if (!isAnalysisEnabled) return AssumptionType.Unknown.asDepType()
    val dependencyTypeOpt = dependencyTypes.headOption.map(_.dependencyType)
    if (dependencyTypeOpt.isDefined) {
      dependencyTypeOpt.get
    } else {
      SiliconRunner.logger.warn(s"WARN: Missing dependency type for $getDebugInfo")
      AssumptionType.Unknown.asDepType()
    }
  }

  def getMergeInfo: DependencyAnalysisMergeInfo = {
    if (!isAnalysisEnabled) return NoDependencyAnalysisMerge()
    mergeInfos.headOption.getOrElse(SimpleDependencyAnalysisMerge(getSourceInfo))
  }

  def getJoinInfo: List[SimpleDependencyAnalysisJoin] = {
    if (!isAnalysisEnabled) return List.empty
    joinInfos.map {
      case EvalStackDependencyAnalysisJoin(joinType, edgeType) =>
        if (sourceInfos.lastOption.isEmpty) SiliconRunner.logger.warn(s"WARN: Missing source info for $getDebugInfo")
        SimpleDependencyAnalysisJoin(sourceInfos.lastOption.orElse(nodes.lastOption.map(DependencyAnalysisSourceInfo.createAnalysisSourceInfo)).getOrElse(StringDependencyAnalysisSourceInfo("Unknown", NoPosition)), joinType, edgeType)
      case a: SimpleDependencyAnalysisJoin => a
    }
  }

  def withMergeInfo(mergeInfo: DependencyAnalysisMergeInfo): DependencyAnalysisInfos = {
    if (!isAnalysisEnabled) return this

    this.copy(mergeInfos = mergeInfo +: mergeInfos)
  }

  def withJoinInfo(joinInfo: DependencyAnalysisJoinInfo): DependencyAnalysisInfos = {
    if (!isAnalysisEnabled) return this

    this.copy(joinInfos = joinInfo +: joinInfos)
  }

  def withEnabled(analysisEnabled: Boolean): DependencyAnalysisInfos = this.copy(analysisEnabled=analysisEnabled)

  def withInfo(sourceInfo: DependencyAnalysisSourceInfo, dependencyType: DependencyType): DependencyAnalysisInfos =
    this.withSource(sourceInfo).withDependencyType(dependencyType)

  def withInfo(sourceInfo: DependencyAnalysisSourceInfo, assumptionType: AssumptionType): DependencyAnalysisInfos =
    this.withSource(sourceInfo).withDependencyType(assumptionType)
}

object DependencyAnalysisInfos {
  val DefaultInfos = DependencyAnalysisInfos(List.empty, List.empty, List.empty, List.empty, List.empty)
}

case class DependencyAnalysisAxiomInfo(analysisInfos: DependencyAnalysisInfos, memberStr: String)
