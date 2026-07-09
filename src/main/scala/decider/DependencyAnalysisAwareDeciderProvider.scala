// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silicon.decider

import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.dependencyAnalysis._
import viper.silicon.state.chunks.{Chunk, GeneralChunk}
import viper.silicon.state.terms.{False, Term, True}
import viper.silicon.verifier.{DependencyAnalysisAwareVerifier, Verifier}
import viper.silver.ast
import viper.silver.ast.Member

trait DependencyAnalysisDeciderFeatures {

  def isDependencyAnalysisEnabled: Boolean

  def initDependencyAnalyzer(member: Member, preambleNodes: Iterable[DependencyAnalysisNode]): Unit
  def getDependencyAnalyzer: DependencyAnalyzer
  def resetDependencyAnalyzer(): Unit

  def registerChunk[CH <: GeneralChunk](buildChunk: Term => CH, perm: Term, analysisInfos: DependencyAnalysisInfos, isExhale: Boolean): CH
  def registerDerivedChunk[CH <: GeneralChunk](sourceChunks: Set[Chunk], buildChunk: Term => CH, perm: Term, analysisInfos: DependencyAnalysisInfos, isExhale: Boolean, createLabel: Boolean = true): CH

  def getOrCreateAnalysisLabelNode(sourceChunks: Iterable[Chunk] = Set.empty, sourceTerms: Iterable[Term] = Set.empty): Option[LabelNode]
}

trait DependencyAnalysisAwareDeciderProvider extends DefaultDeciderProvider { v: DependencyAnalysisAwareVerifier =>
  override def decider: DependencyAnalysisAwareDecider = DADecider

  protected object DADecider extends DependencyAnalysisAwareDecider

  trait DependencyAnalysisAwareDecider extends AbstractDecider with DependencyAnalysisDeciderFeatures {

    override def isDependencyAnalysisEnabled: Boolean = Verifier.config.enableDependencyAnalysis() && !dependencyAnalyzer.isInstanceOf[NoDependencyAnalyzer]

    override def defaultAnalysisInfos: DependencyAnalysisInfos = DependencyAnalysisInfos.DefaultDependencyAnalysisInfos.withEnabled(isDependencyAnalysisEnabled)

    protected var _daProver: DependencyAnalysisAwareZ3ProverStdIO = _
    override def prover: DependencyAnalysisAwareZ3ProverStdIO = _daProver

    override protected def initProver(proverName: String): Unit = {
      _daProver = getProver(proverName)
      _prover = _daProver
    }

    override protected def getProver(prover: String): DependencyAnalysisAwareZ3ProverStdIO = prover match {
      case Z3ProverStdIO.name => new DependencyAnalysisAwareZ3ProverStdIO(uniqueId, termConverter, identifierFactory, reporter)
      case prover =>
        val msg1 = s"Prover '$prover' not supported in combination with the dependency analysis. Defaulting to ${Z3ProverStdIO.name}."
        logger warn msg1
        getProver(Z3ProverStdIO.name)
    }

    private var dependencyAnalyzer: DependencyAnalyzer = new NoDependencyAnalyzer()
    override def getDependencyAnalyzer: DependencyAnalyzer = dependencyAnalyzer

    override def initDependencyAnalyzer(member: Member, preambleNodes: Iterable[DependencyAnalysisNode]): Unit = {
      val isAnalysisEnabled = DependencyAnalyzer.extractEnableAnalysisFromInfo(member.info).getOrElse(Verifier.config.enableDependencyAnalysis())
      if (isAnalysisEnabled) {
        dependencyAnalyzer = new DefaultDependencyAnalyzer(Some(member))
        dependencyAnalyzer.addNodes(preambleNodes)
      } else {
        dependencyAnalyzer = new NoDependencyAnalyzer
      }
    }

    override def resetDependencyAnalyzer(): Unit = {
      dependencyAnalyzer = new NoDependencyAnalyzer
    }

    override protected def assumeWithoutSmokeChecks(termsWithLabel: InsertionOrderedSet[(Term, String)], analysisInfos: DependencyAnalysisInfos, isDefinition: Boolean = false): Unit = {
      super.assumeWithoutSmokeChecks(addAssumptionLabels(termsWithLabel.map(_._1), analysisInfos), analysisInfos, isDefinition)
    }

    def assumeLabel(term: Term, assumptionLabel: String): Unit = {
      pathConditions.addAnalysisLabel(term)
      prover.assume(term, assumptionLabel)
    }

    private def addAssumptionLabels(filteredTerms: Iterable[Term], analysisInfos: DependencyAnalysisInfos) = {
      InsertionOrderedSet(filteredTerms map (t => {
        val assumptionIds = dependencyAnalyzer.addAssumption(t, analysisInfos)
        (t, DependencyAnalyzer.createAssumptionLabel(assumptionIds))
      }))
    }

    override protected def isKnownToBeTrue(t: Term): Boolean = t.equals(True)

    override protected def deciderAssertInternal(asserted: Boolean, t: Term, timeout: Option[Int], analysisInfos: DependencyAnalysisInfos, isCheck: Boolean, label: String = ""): Boolean = {

      val assertNode = if (!asserted) dependencyAnalyzer.createAssertOrCheckNode(t, analysisInfos, isCheck) else None

      val label = DependencyAnalyzer.createAssertionLabel(assertNode map (_.id))

      val result: Boolean = super.deciderAssertInternal(asserted, t, timeout, analysisInfos, isCheck, label)

      if (result) {
        assertNode foreach dependencyAnalyzer.addAssertionNode
      }

      result
    }

    override protected def proverAssert(t: Term, timeout: Option[Mark], label: String): Boolean = {
      val result = super.proverAssert(t, timeout, label)
      if (isPathInfeasible)
        dependencyAnalyzer.addDependency(pcs.getCurrentInfeasibilityNode, Some(DependencyAnalyzer.getIdFromLabel(label)))
      else if (result)
        dependencyAnalyzer.processUnsatCoreAndAddDependencies(prover.getLastUnsatCore, label)
      result
    }

    override def checkSmoke(analysisInfos: DependencyAnalysisInfos, isAssert: Boolean = false): Boolean = {
      val checkNode = dependencyAnalyzer.createAssertOrCheckNode(False, analysisInfos, !isAssert)
      val label = DependencyAnalyzer.createAssertionLabel(checkNode.map(_.id))

      if (isPathInfeasible) {
        checkNode foreach dependencyAnalyzer.addAssertionNode
        dependencyAnalyzer.addDependency(pcs.getCurrentInfeasibilityNode, checkNode.map(_.id))
        return true
      }

      val result = super.checkSmokeInternal(isAssert, label)

      if (result) {
        checkNode foreach dependencyAnalyzer.addAssertionNode
        dependencyAnalyzer.processUnsatCoreAndAddDependencies(prover.getLastUnsatCore, label)
        val infeasibleNodeId = dependencyAnalyzer.addInfeasibilityNode(!isAssert, analysisInfos)
        dependencyAnalyzer.addDependency(checkNode.map(_.id), infeasibleNodeId)
        pcs.setCurrentInfeasibilityNode(infeasibleNodeId)
      } else if (isAssert) {
        checkNode foreach (node => dependencyAnalyzer.addAssertionNode(node.getAssertFailedNode))
      }
      result
    }

    override def handleFailedAssertion(failedAssertion: Term, e: Option[ast.Exp], finalExp: Option[ast.Exp], analysisInfos: DependencyAnalysisInfos, assumeFailedAssertion: Boolean): Unit = {
      dependencyAnalyzer.addAssertionFailedNode(failedAssertion, analysisInfos)
      super.handleFailedAssertion(failedAssertion, e, finalExp, analysisInfos, assumeFailedAssertion)
    }

    override def handleInfeasiblePath(hasAssertions: Boolean, hasAssumptions: Boolean, analysisInfos: DependencyAnalysisInfos): Unit = {
      if (!isPathInfeasible) return
      super.handleInfeasiblePath(hasAssertions, hasAssumptions, analysisInfos)
      if (hasAssertions) {
        dependencyAnalyzer.addAssertionWithDepToInfeasNode(pcs.getCurrentInfeasibilityNode, analysisInfos)
      }
      if (hasAssumptions) {
        dependencyAnalyzer.addAssumption(True, analysisInfos)
      }
    }

    override def registerChunk[CH <: GeneralChunk](buildChunk: Term => CH, perm: Term, analysisInfos: DependencyAnalysisInfos, isExhale: Boolean): CH = {
      registerDerivedChunk(Set.empty, buildChunk, perm, analysisInfos, isExhale)
    }

    override def registerDerivedChunk[CH <: GeneralChunk](sourceChunks: Set[Chunk], buildChunk: Term => CH, perm: Term, analysisInfos: DependencyAnalysisInfos, isExhale: Boolean, createLabel: Boolean = true): CH = {
      if (!isDependencyAnalysisEnabled)
        return buildChunk(perm)

      val labelNodeOpt = getOrCreateAnalysisLabelNode()

      if (isExhale)
        dependencyAnalyzer.registerExhaleChunk(sourceChunks, buildChunk, perm, labelNodeOpt, analysisInfos)
      else {
        dependencyAnalyzer.registerInhaleChunk(sourceChunks, buildChunk, perm, labelNodeOpt, analysisInfos)
      }
    }

    override def getOrCreateAnalysisLabelNode(sourceChunks: Iterable[Chunk] = Set.empty, sourceTerms: Iterable[Term] = Set.empty): Option[LabelNode] = {
      if (!isDependencyAnalysisEnabled)
        return None

      val (label, _) = fresh(ast.LocalVar(DependencyAnalyzer.analysisLabelName, ast.Bool)())
      val labelNode = dependencyAnalyzer.createLabelNode(label, sourceChunks, sourceTerms)
      val smtLabel = DependencyAnalyzer.createAssumptionLabel(labelNode.map(_.id))
      assumeLabel(label, smtLabel)
      labelNode
    }
  }
}
