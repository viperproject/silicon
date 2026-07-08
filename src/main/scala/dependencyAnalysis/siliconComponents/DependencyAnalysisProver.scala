package viper.silicon.dependencyAnalysis.siliconComponents

import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.debugger.DebugAxiom
import viper.silicon.decider.{TermToSMTLib2Converter, Z3ProverStdIO}
import viper.silicon.dependencyAnalysis.{DefaultDependencyAnalyzer, DependencyAnalysisAxiomInfo, DependencyAnalysisNode, DependencyAnalyzer}
import viper.silicon.interfaces.decider.ProverLike
import viper.silicon.state.IdentifierFactory
import viper.silicon.state.terms.Term
import viper.silver.reporter.Reporter

trait DependencyAnalysisProverFeatures extends ProverLike {
  protected val preambleDependencyAnalyzer: DependencyAnalyzer = new DefaultDependencyAnalyzer(None)

  def getPreambleAnalysisNodes: Iterable[DependencyAnalysisNode] = preambleDependencyAnalyzer.getNodes

  def assumeAxiomsWithAnalysisInfo(axioms: InsertionOrderedSet[(Term, DependencyAnalysisAxiomInfo)], description: String): Unit = {
    if (debugMode)
      preambleAssumptions :+= new DebugAxiom(description, axioms.map(_._1))

    axioms.foreach(axiom => {
      val analysisAxiomInfo = axiom._2
      if (analysisAxiomInfo.analysisInfos.analysisEnabled) {
        val id = preambleDependencyAnalyzer.addAxiom(axiom._1, analysisAxiomInfo)
        assume(axiom._1, DependencyAnalyzer.createAxiomLabel(id))
      } else {
        assume(axiom._1, "")
      }
    })
  }
}

class DependencyAnalysisAwareZ3ProverStdIO(uniqueId: String, termConverter: TermToSMTLib2Converter, identifierFactory: IdentifierFactory, reporter: Reporter)
	extends Z3ProverStdIO(uniqueId, termConverter, identifierFactory, reporter) with DependencyAnalysisProverFeatures
