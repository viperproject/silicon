// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silicon.decider

import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.dependencyAnalysis._
import viper.silicon.dependencyAnalysis.graph._
import viper.silicon.state.chunks.{Chunk, GeneralChunk}
import viper.silicon.state.terms.{False, Implies, Term, True}
import viper.silicon.verifier.DependencyAnalysisAwareVerifier
import viper.silver.ast
import viper.silver.dependencyAnalysis.{AdditionalAssertionNode, AdditionalAssumptionNode, AdditionalDependencyNodeInfo, AssumptionType}

trait DependencyAnalysisHandler {

  def getDependencyAnalyzer: DependencyAnalyzer

  def registerChunk[CH <: GeneralChunk](buildChunk: Term => CH, perm: Term, analysisInfos: AnalysisInfos, isExhale: Boolean): CH
  def registerDerivedChunk[CH <: GeneralChunk](sourceChunks: Set[Chunk], buildChunk: Term => CH, perm: Term, analysisInfos: AnalysisInfos, isExhale: Boolean): CH

  def getOrCreateAnalysisLabelNode(sourceChunks: Iterable[Chunk] = Set.empty, sourceTerms: Iterable[Term] = Set.empty): Option[LabelNode]
}

trait DependencyAnalysisAwareDeciderProvider extends DefaultDeciderProvider { v: DependencyAnalysisAwareVerifier =>
  override def decider: DependencyAnalysisAwareDecider = DADecider

  protected object DADecider extends DependencyAnalysisAwareDecider

  trait DependencyAnalysisAwareDecider extends AbstractDecider with DependencyAnalysisHandler {

    override def isDependencyAnalysisEnabledForMember: Boolean = !dependencyAnalyzer.isInstanceOf[NoDependencyAnalyzer]

    override def defaultAnalysisInfos: AnalysisInfos = DependencyAnalysisInfos.DefaultInfos.withEnabled(isDependencyAnalysisEnabledForMember)

    type P = DependencyAnalysisAwareZ3ProverStdIO

    override protected def getProver(prover: String): DependencyAnalysisAwareZ3ProverStdIO = prover match {
      case Z3ProverStdIO.name => new DependencyAnalysisAwareZ3ProverStdIO(uniqueId, termConverter, identifierFactory, reporter)
      case prover =>
        val msg1 = s"Prover '$prover' not supported in combination with the dependency analysis. Defaulting to ${Z3ProverStdIO.name}."
        logger warn msg1
        getProver(Z3ProverStdIO.name)
    }

    private var dependencyAnalyzer: DependencyAnalyzer = new NoDependencyAnalyzer()
    override def getDependencyAnalyzer: DependencyAnalyzer = dependencyAnalyzer

    override def analysisHooks: AnalysisHooks = DependencyAnalysisHooks

    private object DependencyAnalysisHooks extends AnalysisHooks {
      override def beginMember(member: ast.Member, preambleNodes: Iterable[DependencyAnalysisNode]): Unit = {
        val isAnalysisEnabled = DependencyAnalyzer.extractEnableAnalysisFromInfo(member.info).getOrElse(true)
        if (isAnalysisEnabled) {
          dependencyAnalyzer = new DefaultDependencyAnalyzer(Some(member))
          dependencyAnalyzer.addNodes(preambleNodes ++ prover.getPreambleAnalysisNodes)
        } else {
          dependencyAnalyzer = new NoDependencyAnalyzer
        }
      }

      override def endMember(): Unit = {
        dependencyAnalyzer = new NoDependencyAnalyzer
      }

      override def enterNode(analysisInfos: AnalysisInfos, info: ast.Info, node: ast.Node): AnalysisInfos = {
        val newAnalysisInfos = analysisInfos.addInfo(info, node)
        info.getAllInfos[AdditionalDependencyNodeInfo].foreach {
          case AdditionalAssertionNode() => dependencyAnalyzer.createAssertOrCheckNode(True, newAnalysisInfos, isCheck = false).foreach(n => {
            dependencyAnalyzer.addAssertionNode(n)
            if (isPathMarkedInfeasible) dependencyAnalyzer.addDependency(pcs.getCurrentInfeasibilityNode, Some(n.id))
          })
          case AdditionalAssumptionNode() => dependencyAnalyzer.addAssumption(True, newAnalysisInfos)
        }
        newAnalysisInfos
      }

      override def withLabel(term: Term, sourceChunks: Iterable[Chunk], sourceTerms: Iterable[Term]): Term = {
        if (!isDependencyAnalysisEnabledForMember || term.equals(True) || sourceChunks.size + sourceTerms.size == 0)
          term
        else
          getOrCreateAnalysisLabelNode(sourceChunks, sourceTerms).map(n => Implies(n.term, term)).getOrElse(term)
      }

      override def linkMergeInfos(sourceExps: Seq[ast.Exp], targetExps: Seq[ast.Exp]): Unit =
        dependencyAnalyzer.addCustomDependenciesBetweenMergeInfos(sourceExps, targetExps)

      override def recordAssumption(assumption: Term, analysisInfos: AnalysisInfos, description: Option[String]): Unit =
        dependencyAnalyzer.addAssumption(assumption, analysisInfos, description)
    }

    override protected def assumeWithoutSmokeChecks(terms: InsertionOrderedSet[Term], analysisInfos: AnalysisInfos, isDefinition: Boolean = false): Unit = {
      /* Registered up front since assumptions on infeasible paths must be recorded too, even though they never reach the prover. */
      val labels = registerAssumptions(terms, analysisInfos)
      assumeWithoutSmokeChecksInternal(terms, isDefinition)(t => prover.assume(t, labels(t)))
    }

    def assumeLabel(term: Term, assumptionLabel: Option[String]): Unit = {
      pathConditions.addAnalysisLabel(term)
      prover.assume(term, assumptionLabel)
    }

    private def registerAssumptions(terms: InsertionOrderedSet[Term], analysisInfos: AnalysisInfos): Map[Term, Option[String]] = {
      terms.toSeq.map(t => {
        val assumptionIds = dependencyAnalyzer.addAssumption(t, analysisInfos)
        (t, DependencyAnalyzer.createAssumptionLabel(assumptionIds))
      }).toMap
    }

    override protected def isKnownToBeTrue(t: Term): Boolean = t.equals(True)

    override protected def deciderAssertInternal(t: Term, timeout: Option[Int], analysisInfos: AnalysisInfos, isCheck: Boolean): Boolean = {
      val assertNode = dependencyAnalyzer.createAssertOrCheckNode(t, analysisInfos, isCheck)
      val label = DependencyAnalyzer.createAssertionLabel(assertNode map (_.id))

      val result = proverAssert(t, timeout)(prover.assert(t, timeout, label))

      if (isPathMarkedInfeasible)
        dependencyAnalyzer.addDependency(pcs.getCurrentInfeasibilityNode, assertNode map (_.id))
      else if (result)
        assertNode foreach (node => dependencyAnalyzer.processUnsatCoreAndAddDependencies(prover.getLastUnsatCore, node.id))

      if (result) {
        assertNode foreach dependencyAnalyzer.addAssertionNode
      }

      result
    }

    override protected def failedAssertionInfos(analysisInfos: AnalysisInfos): AnalysisInfos =
      analysisInfos.overrideDependencyType(AssumptionType.Explicit)

    override def checkSmoke(analysisInfos: AnalysisInfos, isAssert: Boolean = false): Boolean = {
      val checkNode = dependencyAnalyzer.createAssertOrCheckNode(False, analysisInfos, !isAssert)

      if (isPathMarkedInfeasible) {
        checkNode foreach dependencyAnalyzer.addAssertionNode
        dependencyAnalyzer.addDependency(pcs.getCurrentInfeasibilityNode, checkNode.map(_.id))
        true
      } else {
        val result = checkSmokeInternal(isAssert)

        if (result) {
          checkNode foreach dependencyAnalyzer.addAssertionNode
          checkNode foreach (node => dependencyAnalyzer.processUnsatCoreAndAddDependencies(prover.getLastUnsatCore, node.id))
          val infeasibleNodeId = dependencyAnalyzer.addInfeasibilityNode(!isAssert, analysisInfos)
          dependencyAnalyzer.addDependency(checkNode.map(_.id), infeasibleNodeId)
          pcs.setCurrentInfeasibilityNode(infeasibleNodeId)
        } else if (isAssert) {
          checkNode foreach (node => dependencyAnalyzer.addAssertionNode(node.getAssertFailedNode))
        }
        result
      }
    }

    override def handleFailedAssertion(failedAssertion: Term, e: Option[ast.Exp], finalExp: Option[ast.Exp], analysisInfos: AnalysisInfos, assumeFailedAssertion: Boolean): Unit = {
      dependencyAnalyzer.addAssertionFailedNode(failedAssertion, analysisInfos)
      super.handleFailedAssertion(failedAssertion, e, finalExp, analysisInfos, assumeFailedAssertion)
    }

    override def handleInfeasiblePath(hasAssertions: Boolean, hasAssumptions: Boolean, analysisInfos: AnalysisInfos): Unit = {
      if (!isPathMarkedInfeasible) return
      super.handleInfeasiblePath(hasAssertions, hasAssumptions, analysisInfos)
      if (hasAssertions) {
        dependencyAnalyzer.addAssertionWithDepToInfeasNode(pcs.getCurrentInfeasibilityNode, analysisInfos)
      }
      if (hasAssumptions) {
        dependencyAnalyzer.addAssumption(True, analysisInfos)
      }
    }

    override def registerChunk[CH <: GeneralChunk](buildChunk: Term => CH, perm: Term, analysisInfos: AnalysisInfos, isExhale: Boolean): CH = {
      registerDerivedChunk(Set.empty, buildChunk, perm, analysisInfos, isExhale)
    }

    override def registerDerivedChunk[CH <: GeneralChunk](sourceChunks: Set[Chunk], buildChunk: Term => CH, perm: Term, analysisInfos: AnalysisInfos, isExhale: Boolean): CH = {
      if (!isDependencyAnalysisEnabledForMember)
        return buildChunk(perm)

      val labelNodeOpt = getOrCreateAnalysisLabelNode(sourceChunks)

      if (isExhale)
        dependencyAnalyzer.registerExhaleChunk(buildChunk, perm, labelNodeOpt, analysisInfos)
      else {
        dependencyAnalyzer.registerInhaleChunk(buildChunk, perm, labelNodeOpt, analysisInfos)
      }
    }

    override def getOrCreateAnalysisLabelNode(sourceChunks: Iterable[Chunk] = Set.empty, sourceTerms: Iterable[Term] = Set.empty): Option[LabelNode] = {
      if (!isDependencyAnalysisEnabledForMember)
        return None

      val (label, _) = fresh(ast.LocalVar(DependencyAnalyzer.analysisLabelName, ast.Bool)())
      val labelNode = dependencyAnalyzer.createLabelNode(label, sourceChunks, sourceTerms)
      val smtLabel = DependencyAnalyzer.createAssumptionLabel(labelNode.map(_.id))
      assumeLabel(label, smtLabel)
      labelNode
    }
  }
}
