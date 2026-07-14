// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silicon.dependencyAnalysis.graphInterpretation

import viper.silicon.dependencyAnalysis._
import viper.silicon.dependencyAnalysis.graphInterpretation.DATraversalMode.DATraversalMode
import viper.silver.dependencyAnalysis.{AnalysisSourceInfo, AssumptionType}

import scala.collection.mutable

class DependencyAnalysisProgressSupporter[T <: DependencyGraphState](interpreter: DependencyGraphInterpreter[T]) {

  private val dependencyGraph = interpreter.getGraph
  private lazy val sourceToAssertionNodesMap: Map[AnalysisSourceInfo, Set[DependencyAnalysisNode]] = interpreter.getNonInternalAssertionNodes.groupBy(_.sourceInfo)

  def computeVerificationProgress(enableDebugging: Boolean = false): (VerificationProgress, VerificationProgress) = {
    computeVerificationProgressOptimized(enableDebugging)
  }

  /**
   * Computes all dependencies of a given dependency node. Intermediate results are cached at procedure-boundaries.
   * That is, the dependencies of each pre- and postcondition are cached and can thus be reused for subsequent computations.
   * We do not cache intraprocedural dependencies to allow for precise computation of dependencies using the low-level graph.
   */
  val deps: DAMemo[(AnalysisSourceInfo, DATraversalMode), Set[CompactUserLevelDependencyAnalysisNode]] = DAMemo { case (assertionNode, mode) =>
    // TODO ake: maybe this should be moved to the DependencyGraphInterpreter such that other queries can be optimized as well.
    def computeDependencies(currentNode: AnalysisSourceInfo, visited: Set[(AnalysisSourceInfo, DATraversalMode)], traversalMode: DATraversalMode): Set[CompactUserLevelDependencyAnalysisNode] = {
      if (visited.contains((currentNode, traversalMode))) {
        return Set.empty // break cycles to avoid infinite loops
      }

      if (deps.contains(currentNode, traversalMode)) {
        return deps((currentNode, traversalMode))
      }

      val updatedVisited = visited ++  Set((currentNode, traversalMode))
      val allNonInternalAssertions = sourceToAssertionNodesMap.getOrElse(currentNode, Set.empty)

      // compute intraprocedural dependencies without caching any intermediate results
      val intraMethodDependencyIds = dependencyGraph.getAllDependencies(allNonInternalAssertions.map(_.id), includeInfeasibilityNodes=true, includeUpwardEdges=false, includeDownwardEdges=false)
      val intraMethodDependencies = intraMethodDependencyIds.flatMap(interpreter.nonInternalAssumptionNodesMap.get).filterNot(_.sourceInfo.equals(currentNode))

      // recursively compute all interprocedural dependencies and cache results at procedure-boundaries
      val relevantInterProceduralEdges = traversalMode match {
        case DATraversalMode.Upwards   => dependencyGraph.getEdgesConnectingMethodsUpwards
        case DATraversalMode.Downwards => dependencyGraph.getEdgesConnectingMethodsDownwards
      }
      val interProceduralNodeIds = intraMethodDependencyIds.flatMap(n => relevantInterProceduralEdges.getOrElse(n, Set.empty))
      val interProceduralNodes = interProceduralNodeIds.flatMap(interpreter.nodesMap.get)
      val interProceduralDependencies = interProceduralNodes.map(_.sourceInfo).filterNot(_.equals(currentNode)).flatMap(node => computeDependencies(node, updatedVisited, traversalMode))

      // put together all identified dependencies and cache the result
      val result = reduceCompactUserLevelNodes(toCompactUserLevelNodes(intraMethodDependencies ++ interProceduralNodes) ++ interProceduralDependencies)
      deps.put((currentNode, traversalMode), result)
      result
    }

    computeDependencies(assertionNode, Set.empty, mode)
  }

  // merges results of several computations by merging low-level nodes belonging to the same source
  private def reduceCompactUserLevelNodes(inputNodes: Set[CompactUserLevelDependencyAnalysisNode]): Set[CompactUserLevelDependencyAnalysisNode] = {

    val resultMap: mutable.Map[AnalysisSourceInfo, CompactUserLevelDependencyAnalysisNode] = mutable.Map()

    for (node <- inputNodes) {
      val existingNode = resultMap.get(node.source)

      val newNode = existingNode match {
        case Some(existing) =>
          CompactUserLevelDependencyAnalysisNode(
            source = node.source,
            assumptionTypes = existing.assumptionTypes ++ node.assumptionTypes,
            assertionTypes = existing.assertionTypes ++ node.assertionTypes,
            hasFailures = existing.hasFailures || node.hasFailures
          )
        case None => node
      }

      resultMap.update(node.source, newNode)
    }

    resultMap.values.toSet
  }

  private def toCompactUserLevelNodes(lowLevelNodes: Set[DependencyAnalysisNode]): Set[CompactUserLevelDependencyAnalysisNode] = {
    lowLevelNodes.groupBy(_.sourceInfo).map { case (source, nodes) =>
      val assertionNodes = nodes.filter(_.isInstanceOf[GeneralAssertionNode])
      CompactUserLevelDependencyAnalysisNode(source,
        nodes.filter(_.isInstanceOf[GeneralAssumptionNode]).map(_.assumptionType),
        assertionNodes.map(_.assumptionType),
        assertionNodes.exists(_.asInstanceOf[GeneralAssertionNode].hasFailed)
      )}.toSet
  }

  /**
   * Computes the assertion quality given an assertion node and all of its dependencies.
   * It returns None if the assertion trivially verifies (it has no dependencies). Otherwise, it returns the assertion quality.
   * If the assertion encountered a failure, i.e. it could not be proven to hold, then the assertion quality is 0.0.
   * Otherwise, the assertion quality is defined as the fraction of non-assumption dependencies over all dependencies.
   */
  private def computeAssertionQuality(allDependencies: Set[CompactUserLevelDependencyAnalysisNode], assertion: AnalysisSourceInfo): Option[Double] = {
    val assertionNodes = sourceToAssertionNodesMap.getOrElse(assertion, Set.empty).filter(node => node.isInstanceOf[GeneralAssertionNode])
    val failedAssertionNodes = assertionNodes.filter(node => node.asInstanceOf[GeneralAssertionNode].hasFailed || node.assumptionType.equals(AssumptionType.ExplicitPostcondition))
    // assertions with failures have quality of 0.0
    if (failedAssertionNodes.nonEmpty)
      return Some(0.0)

    if (allDependencies.isEmpty) return None // we filter out trivial assertions, e.g. assertions that do not have any dependencies

    val explicitDeps = allDependencies.filter(_.assumptionTypes.intersect(AssumptionType.explicitAssumptionTypes).nonEmpty).map(_.source)
    val numDepsTotal = allDependencies.size
    Some((numDepsTotal - explicitDeps.size).toDouble / numDepsTotal.toDouble)
  }

  private def getAssertionsRelevantForProgress: Map[AnalysisSourceInfo, Set[DependencyAnalysisNode]] = {
    val excludedAssertionTypes = AssumptionType.importedTypes ++ AssumptionType.preconditionTypes
    sourceToAssertionNodesMap.filter(ass => ass._2.map(_.assumptionType).intersect(excludedAssertionTypes).isEmpty)
  }

  /**
   * @return the verification progress of the entire program.
   *         Verification progress is defined as the product of specification quality and proof quality.
   *         Specification quality is the fraction of source code statements that is a dependency of any proof obligation.
   *         Proof quality is defined as the average assertion quality over all proof obligations.
   *         Assertion quality of an assertion a is the fraction of non-assumption dependencies over all dependencies of the assertion a.
   */
  def computeVerificationProgressOptimized(enableDebugOutput: Boolean = false): (VerificationProgress, VerificationProgress) = {

    // compute all dependencies of each proof obligation
    val allAssertions = getAssertionsRelevantForProgress.keySet.toList
    val allDependenciesPerAssertionNode = allAssertions map (ass => ({
      val ups = deps((ass, DATraversalMode.Upwards))
      val downs = deps((ass, DATraversalMode.Downwards))
      reduceCompactUserLevelNodes(ups ++ downs)
    }, ass))

    val specQuality = computeSpecQuality(allDependenciesPerAssertionNode.flatMap(_._1).toSet, enableDebugOutput)

    val assertionQualities = allDependenciesPerAssertionNode map (ass => (computeAssertionQuality(ass._1, ass._2), ass._2)) collect { case (Some(q), s) => (q, s) }
    val numNonTrivialAssertions = assertionQualities.size

    // compute Peter's proof quality
    val fullyVerifiedAssertions = assertionQualities.filter(_._1 == 1.0)
    val proofQualityPeter = if (numNonTrivialAssertions > 0) fullyVerifiedAssertions.size.toDouble / numNonTrivialAssertions.toDouble else 1.0

    // compute Lea's proof quality
    val assertionQualitiesSum = assertionQualities.map(_._1).sum
    val proofQualityLea = if (numNonTrivialAssertions > 0) assertionQualitiesSum / numNonTrivialAssertions.toDouble else 1.0

    if (enableDebugOutput)
      println(
        s"fullyVerifiedAssertions:\n\t${fullyVerifiedAssertions.sortBy(n => (n._2.getLineNumber, n._2.toString)).mkString("\n\t")}\n" +
        s"assertionQualitiesSum:\n\t${assertionQualities.sortBy(n => (n._2.getLineNumber, n._2.toString)).mkString("\n\t")}"
      )

    println(
      s"specQuality = $specQuality\n" +
        s"proof quality (Peter): ${fullyVerifiedAssertions.size} / $numNonTrivialAssertions = $proofQualityPeter\n" +
        s"proof quality (Lea): $assertionQualitiesSum / $numNonTrivialAssertions = $proofQualityLea\n"
    )

    val progressPeter = VerificationProgress(specQuality, proofQualityPeter)
    val progressLea = VerificationProgress(specQuality, proofQualityLea)
    (progressPeter, progressLea)
  }


  /**
   * Computes the specification quality given the covered nodes. Specification quality is defined as the fraction of
   * all (user-level) nodes in the graph that are covered.
   */
  private def computeSpecQuality(coveredNodes: Set[CompactUserLevelDependencyAnalysisNode], enableDebugOutput: Boolean = false): Double = {

    val explicitAssertions = toCompactUserLevelNodes(interpreter.getExplicitAssertionNodes)
    val allSourceCodeNodes = toCompactUserLevelNodes(interpreter.getNonInternalAssumptionNodes).filter(n => AssumptionType.sourceCodeTypes.intersect(n.assumptionTypes).nonEmpty).map(_.source).diff(explicitAssertions.map(_.source))

    if (allSourceCodeNodes.isEmpty) return 1.0

    val coveredSourceCodeNodes = coveredNodes.map(_.source).intersect(allSourceCodeNodes)
    if (enableDebugOutput)
        println(
          s"Covered Source Code:\n\t${coveredSourceCodeNodes.toList.sortBy(n => (n.getLineNumber, n.toString())).mkString("\n\t")}\n" +
          s"Uncovered Source Code:\n\t${allSourceCodeNodes.diff(coveredSourceCodeNodes).toList.sortBy(n => (n.getLineNumber, n.toString())).mkString("\n\t")}"
        )

    println(s"Spec Quality = ${coveredSourceCodeNodes.size} / ${allSourceCodeNodes.size}")
    coveredSourceCodeNodes.size.toDouble / allSourceCodeNodes.size.toDouble
  }


  /**
   * @return a list of assumption nodes ordered by their impact on proof quality.
   */
  def computeAssumptionRanking(): List[(String, Double)] = {
    val allAssertions = interpreter.toUserLevelNodes(getAssertionsRelevantForProgress.values.flatten)

    val relevantDependenciesPerAssertion = allAssertions
      .map(ass => (ass, interpreter.toUserLevelNodes(interpreter.getAllNonInternalDependencies(ass.lowerLevelNodes.map(_.id))).diffBySource(Set(ass)))).toMap
      .filter { case (assertion, assumptions) => assumptions.nonEmpty || assertion.hasFailures || assertion.assertionTypes.contains(AssumptionType.ExplicitPostcondition) }
    val numAssertions = relevantDependenciesPerAssertion.size.toDouble

    val assumptionImpacts = relevantDependenciesPerAssertion.toList.flatMap { case (_, assumptions) =>
      val explicitDeps = UserLevelDependencyAnalysisNode.extractByAssumptionType(assumptions, AssumptionType.explicitAssumptionTypes)
      explicitDeps.map(node => (node.source, 1.0 / assumptions.size / numAssertions)).toList
    }

    val unverifiedAssertionImpacts = getAssertionsWithZeroQuality.map(assertion => (assertion, 1.0 / numAssertions)).toList

    val totalImpacts1 = (assumptionImpacts ++ unverifiedAssertionImpacts).groupBy(_._1)
    val totalImpacts = totalImpacts1.map { case (assumption, impacts) => (assumption.toString, impacts.map(_._2).sum) }.toList

    totalImpacts.sortBy(_._2).reverse
  }

  private def getAssertionsWithZeroQuality: Set[AnalysisSourceInfo] = {
    val allAssertions = interpreter.toUserLevelNodes(interpreter.getNonInternalAssertionNodes)
    allAssertions.filter(assertion => assertion.hasFailures || assertion.assertionTypes.contains(AssumptionType.ExplicitPostcondition)).getSourceSet()
  }

  /**
   * Returns all uncovered source code statements.
   */
  def computeUncoveredStatementsPerMember(): Map[String, List[AnalysisSourceInfo]] = {
    val allAssertions = interpreter.toUserLevelNodes(getAssertionsRelevantForProgress.values.flatten)
    val allDependencies = allAssertions.flatMap(ass => interpreter.toUserLevelNodes(interpreter.getAllNonInternalDependencies(ass.lowerLevelNodes.map(_.id))).diffBySource(Set(ass))).getSourceMemberSet()

    val explicitAssertions = interpreter.toUserLevelNodes(interpreter.getExplicitAssertionNodes)
    val allNodes = interpreter.toUserLevelNodes(interpreter.getNonInternalAssumptionNodes)
    val allSourceCodeStmts = UserLevelDependencyAnalysisNode.extractByAssumptionType(allNodes, AssumptionType.sourceCodeTypes).getSourceMemberSet().diff(explicitAssertions.getSourceMemberSet())

    val uncoveredSourceCodeStmts = allSourceCodeStmts.diff(allDependencies)
    uncoveredSourceCodeStmts.groupBy(_._2).map { case (member, sources) =>
      (member, sources.map(_._1).toList.sortBy(_.getLineNumber))
    }
  }
}

case class DAMemo[A,B](f: A => B) extends (A => B) {
  private val cache = mutable.Map.empty[A, B]
  def apply(x: A): B = cache getOrElseUpdate (x, f(x))

  def put(a: A, b: B): Option[B] = {
    cache.put(a, b)
  }

  def contains(a: A): Boolean = {
    cache.contains(a)
  }
}

case class VerificationProgress(specQuality: Double, proofQuality: Double) {
  lazy val progress = specQuality * proofQuality
}
