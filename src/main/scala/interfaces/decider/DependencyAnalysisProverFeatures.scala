package viper.silicon.interfaces.decider

import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.debugger.DebugAxiom
import viper.silicon.dependencyAnalysis.{DependencyAnalysisAxiomInfo, DependencyAnalysisNode, DependencyAnalyzer}
import viper.silicon.state.terms.Term

trait DependencyAnalysisProverFeatures extends ProverLike {
  protected var preambleDependencyAnalyzer: DependencyAnalyzer

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
