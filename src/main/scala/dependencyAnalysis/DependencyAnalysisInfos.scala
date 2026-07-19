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

  private def isAnalysisEnabled = Verifier.config.dependencyAnalysis.isDefined && analysisEnabled

  def addInfo(info: ast.Info, node: ast.Node): DependencyAnalysisInfos = {
    if (isAnalysisEnabled) {
      val newSourceInfos = sourceInfos ++ info.getUniqueInfo[DependencyAnalysisSourceInfo].toList
      val newDependencyInfos = dependencyTypes ++ info.getUniqueInfo[DependencyTypeInfo].toList
      val newMergeInfos = mergeInfos ++ info.getUniqueInfo[DependencyAnalysisMergeInfo].toList
      val newJoinInfos = joinInfos ++ info.getUniqueInfo[DependencyAnalysisJoinInfo].toList
      this.copy(sourceInfos=newSourceInfos, dependencyTypes=newDependencyInfos, mergeInfos=newMergeInfos, joinInfos=newJoinInfos, nodes=nodes ++ List(node))
    } else {
      this
    }
  }

  def addInfo(info: ast.Info): DependencyAnalysisInfos = {
    if (isAnalysisEnabled) {
      val newSourceInfos = sourceInfos ++ info.getUniqueInfo[DependencyAnalysisSourceInfo].toList
      val newDependencyInfos = dependencyTypes ++ info.getUniqueInfo[DependencyTypeInfo].toList
      val newMergeInfos = mergeInfos ++ info.getUniqueInfo[DependencyAnalysisMergeInfo].toList
      val newJoinInfos = joinInfos ++ info.getUniqueInfo[DependencyAnalysisJoinInfo].toList
      this.copy(sourceInfos=newSourceInfos, dependencyTypes=newDependencyInfos, mergeInfos=newMergeInfos, joinInfos=newJoinInfos)
    } else {
      this
    }
  }

  def addInfo(infoString: String, pos: ast.Position, dependencyType: DependencyType): DependencyAnalysisInfos = if (isAnalysisEnabled) {
    this.copy(sourceInfos = sourceInfos ++ List(StringDependencyAnalysisSourceInfo(infoString, pos)), dependencyTypes = dependencyTypes ++ List(DependencyTypeInfo(dependencyType)))
  } else {
    this
  }

  def withDependencyType(dependencyType: DependencyType): DependencyAnalysisInfos = {
    if (isAnalysisEnabled) this.copy(dependencyTypes = DependencyTypeInfo(dependencyType) +: dependencyTypes)
    else this
  }

  def withDependencyType(assumptionType: AssumptionType): DependencyAnalysisInfos = {
    if (isAnalysisEnabled) this.copy(dependencyTypes = DependencyTypeInfo(DependencyType(assumptionType)) +: dependencyTypes)
    else this
  }

  def withSource(source: DependencyAnalysisSourceInfo): DependencyAnalysisInfos =
    if (isAnalysisEnabled) this.copy(sourceInfos = source +: sourceInfos) else this

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
    if (isAnalysisEnabled) {
      val sourceInfoOpt = sourceInfos.headOption
      if (sourceInfoOpt.isDefined) {
        sourceInfoOpt.get
      } else {
        SiliconRunner.logger.warn(s"WARN: Missing source info for $getDebugInfo")
        nodes.headOption.map(DependencyAnalysisSourceInfo.createAnalysisSourceInfo).getOrElse(StringDependencyAnalysisSourceInfo("Unknown", NoPosition))
      }
    } else {
      StringDependencyAnalysisSourceInfo("Unknown", NoPosition)
    }
  }

  def getDependencyType: DependencyType = {
    if (isAnalysisEnabled) {
      val dependencyTypeOpt = dependencyTypes.headOption.map(_.dependencyType)
      if (dependencyTypeOpt.isDefined) {
        dependencyTypeOpt.get
      } else {
        SiliconRunner.logger.warn(s"WARN: Missing dependency type for $getDebugInfo")
        AssumptionType.Unknown.asDepType()
      }
    } else {
      AssumptionType.Unknown.asDepType()
    }
  }

  def getMergeInfo: DependencyAnalysisMergeInfo = {
    if (isAnalysisEnabled) mergeInfos.headOption.getOrElse(SimpleDependencyAnalysisMerge(getSourceInfo))
    else NoDependencyAnalysisMerge()
  }

  def getJoinInfo: List[SimpleDependencyAnalysisJoin] = {
    if (isAnalysisEnabled) {
      joinInfos.map {
        case EvalStackDependencyAnalysisJoin(joinType, edgeType) =>
          if (sourceInfos.lastOption.isEmpty) SiliconRunner.logger.warn(s"WARN: Missing source info for $getDebugInfo")
          SimpleDependencyAnalysisJoin(sourceInfos.lastOption.orElse(nodes.lastOption.map(DependencyAnalysisSourceInfo.createAnalysisSourceInfo)).getOrElse(StringDependencyAnalysisSourceInfo("Unknown", NoPosition)), joinType, edgeType)
        case a: SimpleDependencyAnalysisJoin => a
      }
    } else List.empty
  }

  def withMergeInfo(mergeInfo: DependencyAnalysisMergeInfo): DependencyAnalysisInfos =
    if (isAnalysisEnabled) this.copy(mergeInfos = mergeInfo +: mergeInfos) else this

  def withJoinInfo(joinInfo: DependencyAnalysisJoinInfo): DependencyAnalysisInfos =
    if (isAnalysisEnabled) this.copy(joinInfos = joinInfo +: joinInfos) else this

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
