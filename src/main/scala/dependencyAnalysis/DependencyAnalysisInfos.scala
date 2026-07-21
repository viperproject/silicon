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

/*
  Why taking the first SOURCE INFO and DEPENDENCY TYPE that was encountered?
    First, nodes created while evaluating a subexpression are considered to be part of its parent expression/statement.
      This follows our definition saying that if a statement is executed, it is fully executed, thus requiring all proof obligations of all subexpressions
      and introducing all assumptions of all subexpressions. Similarly, an expression is always fully evaluated.
    Second, some statements/expressions introduce proof obligations and assumptions taken from another source.
      For example, method calls require the proof of all preconditions, which are taken from the method declaration. The source info of these preconditions
      is different from the method call, but we still want the resulting proof obligations to be represented as part of the method call's node.
      In this case, we have to consider the first source info (the method call) for the dependency nodes. For debugging purposes, it is valuable
      to keep track of the precondition's sources anyway, although they are irrelevant for the dependency nodes. Similarly, the dependency type of
      preconditions is different from the dependency type of method calls. We should consider the one from the method calls.
    Also note that Silicon already handles composed statements (if, while, seqn) and invokes exec only on single statements, which is why we do
      not need to handle these cases. Similarly, expressions are split into their top-level conjuncts whenever appropriate.

    What are MERGE INFOS and how do I use them?
      The merge infos are one of the main measures to make the analysis more precise. It indicates which edges, that are not already discovered through
      UNSAT cores, are added to intra-procedural graphs. All nodes with the same merge info are interconnected, i.e. all its assumption nodes depend on (have an edge to)
      all its assertion nodes. By default, the merge info is identical to the source info. However, we can control this behavior
      by setting custom merge infos. Nodes can have arbitrarily many merge infos, e.g. some nodes have merge info A, some have B,
      and some have both thus connecting A and B in a controlled manner. An example usage can be found for field assignments (DefaultHeapSupportRules.execFieldAssign).

    What are JOIN INFOS and how do I use them?
      Join infos specify how intra-procedural graphs are joined to obtain the final (interprocedural) dependency graph.
      They are mainly attached to method and function calls, and pre/postconditions, but they might be defined by frontends already
      and thus be propagated as part of the Viper AST node's info field.
 */

/**
 * Stores all information about the currently evaluated/executed Viper AST node. This info is used to derive the parameters for the low-level dependency nodes.
 *
 * @param sourceInfos list of sourceInfos encountered during execution/evaluation of the current Viper AST node.
 *                    The head of the list corresponds to the first source info that was encountered (unless it got overridden at some point).
 *                    This head is used as the sourceInfo when creating dependency nodes, indicating the user-level dependency node they belong to.
 *                    The tail of sourceInfos is mainly used for debugging purposes or might be used for more fine-grained tracking in the future.
 *                    The source info should always be set when creating nodes. Otherwise, the analysis might be unsound.
 * @param dependencyTypes list of dependencyTypes encountered during execution/evaluation of the current Viper AST node.
 *                        Similarly to sourceInfos, the head is the first dependency type encountered (unless overridden) and determines the
 *                        dependency type when creating dependency nodes. We keep the tail for debugging purposes.
 *                        The dependency type should always be set when creating nodes. Otherwise, the analysis might be unsound.
 * @param mergeInfos list of mergeInfos encountered during execution/evaluation of the current Viper AST node.
 *                   They indicate which edges need to be added to the low-level, intraprocedural graph.
 *                   All merge infos are relevant and thus propagated to newly created dependency nodes.
 *                   If mergeInfos is empty, the head of sourceInfos determines the dependency node's merge info.
 * @param joinInfos list of joinInfos encountered during execution/evaluation of the current Viper AST node.
 *                  They indicate how to join graphs of different procedures.
 *                  All join infos are relevant and thus propagated to newly created dependency nodes.
 *                  If join infos is empty, dependency nodes are created without join infos, thus they are irrelevant for joining graphs.
 * @param nodes  list of Viper AST nodes indicating the evaluation stack. The head of this list corresponds to the current Viper AST node being evaluated/executed.
 *              The tail indicates its subexpressions in the order they got evaluated.
 * @param analysisEnabled boolean flag indicating whether the analysis is currently enabled; might change at runtime.
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

  def overrideDependencyType(dependencyType: DependencyType): DependencyAnalysisInfos = {
    if (isAnalysisEnabled) this.copy(dependencyTypes = DependencyTypeInfo(dependencyType) +: dependencyTypes)
    else this
  }

  def overrideDependencyType(assumptionType: AssumptionType): DependencyAnalysisInfos = {
    if (isAnalysisEnabled) this.copy(dependencyTypes = DependencyTypeInfo(DependencyType(assumptionType)) +: dependencyTypes)
    else this
  }

  def overrideSourceInfo(source: DependencyAnalysisSourceInfo): DependencyAnalysisInfos =
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
    this.overrideSourceInfo(sourceInfo).overrideDependencyType(dependencyType)

  def withInfo(sourceInfo: DependencyAnalysisSourceInfo, assumptionType: AssumptionType): DependencyAnalysisInfos =
    this.overrideSourceInfo(sourceInfo).overrideDependencyType(assumptionType)
}

object DependencyAnalysisInfos {
  val DefaultInfos = DependencyAnalysisInfos(List.empty, List.empty, List.empty, List.empty, List.empty)
}

case class DependencyAnalysisAxiomInfo(analysisInfos: DependencyAnalysisInfos, memberStr: String)
