package dependencyAnalysis

import viper.silicon.dependencyAnalysis.{AnalysisSourceInfo, AssumptionType, DependencyAnalysisNode, GeneralAssertionNode, GeneralAssumptionNode, StringAnalysisSourceInfo}
import viper.silicon.dependencyAnalysis.AssumptionType.AssumptionType
import viper.silicon.state.terms.{And, Term}
import viper.silver.ast.Position

object UserLevelDependencyAnalysisNode {

  def from(dependencyNodes: Iterable[DependencyAnalysisNode]): Set[UserLevelDependencyAnalysisNode] = {
    val res = dependencyNodes
      .map(n => (StringAnalysisSourceInfo(n.sourceInfo.getDescription, n.sourceInfo.getPosition), n))
      .groupBy(_._1).map { case (key, nodes) =>
      UserLevelDependencyAnalysisNode(key, nodes.map(_._2).toSet)
    }.toSet
    res
  }

  def extractExplicitAssumptionNodes(nodes: Set[UserLevelDependencyAnalysisNode]): Set[UserLevelDependencyAnalysisNode] = {
    extractByAssumptionType(nodes, AssumptionType.explicitAssumptionTypes)
  }

  def extractNonExplicitAssumptionNodes(nodes: Set[UserLevelDependencyAnalysisNode]): Set[UserLevelDependencyAnalysisNode] = {
    nodes.diff(extractExplicitAssumptionNodes(nodes))
  }

  def extractVerificationAnnotationNodes(nodes: Set[UserLevelDependencyAnalysisNode]): Set[UserLevelDependencyAnalysisNode] = {
    extractByAssumptionType(nodes, AssumptionType.verificationAnnotationTypes)
  }

  def extractSourceCodeNodes(nodes: Set[UserLevelDependencyAnalysisNode]): Set[UserLevelDependencyAnalysisNode] = {
    nodes.diff(extractExplicitAssumptionNodes(nodes)).diff(extractVerificationAnnotationNodes(nodes))
  }

  def extractByAssumptionType(nodes: Set[UserLevelDependencyAnalysisNode], assumptionTypes: Set[AssumptionType]): Set[UserLevelDependencyAnalysisNode] = {
    nodes.filter(node => assumptionTypes.intersect(node.assumptionTypes).nonEmpty)
  }

  def extractByAssertionType(nodes: Set[UserLevelDependencyAnalysisNode], assertionTypes: Set[AssumptionType]): Set[UserLevelDependencyAnalysisNode] = {
    nodes.filter(node => assertionTypes.intersect(node.assertionTypes).nonEmpty)
  }

  def mkString(nodes: Set[UserLevelDependencyAnalysisNode], sep: String = "\n"): String = {
    nodes.toList.sortBy(_.source.getLineNumber).mkString(sep)
  }

  def mkUserLevelString(nodes: Set[DependencyAnalysisNode], sep: String = "\n"): String = {
    mkString(from(nodes), sep)
  }

  implicit class SetNodeOps(private val left: Set[UserLevelDependencyAnalysisNode]) extends AnyVal {
    def diffBySource(right: Set[UserLevelDependencyAnalysisNode]): Set[UserLevelDependencyAnalysisNode] = {
      val sources = right.map(_.groupingCondition)
      left.filterNot(n => sources.contains(n.groupingCondition))
    }

    def getSourceSet(): Set[AnalysisSourceInfo] = {
      left.map(_.source)
    }
  }
}

case class UserLevelDependencyAnalysisNode(source: AnalysisSourceInfo, lowerLevelNodes: Set[DependencyAnalysisNode]) {

  def position: Position = source.getPosition

  def assumptionTypes: Set[AssumptionType] = lowLevelAssumptionNodes.map(_.assumptionType)
  def assertionTypes: Set[AssumptionType] = lowLevelAssertionNodes.map(_.assumptionType)

  lazy val lowLevelAssumptionNodes: Set[DependencyAnalysisNode] = lowerLevelNodes.filter(_.isInstanceOf[GeneralAssumptionNode])
  lazy val lowLevelAssertionNodes: Set[DependencyAnalysisNode] = lowerLevelNodes.filter(_.isInstanceOf[GeneralAssertionNode])

  lazy val assumptionTerm: Term = And(lowLevelAssumptionNodes.map(_.getTerm))
  lazy val assertionTerm: Term = And(lowLevelAssertionNodes.map(_.getTerm))

  lazy val hasFailures: Boolean = lowerLevelNodes.filter(_.isInstanceOf[GeneralAssertionNode]).map(_.asInstanceOf[GeneralAssertionNode]).exists(_.hasFailed)


  override def toString: String = source.toString

  def groupingCondition: (String, Position) = (source.toString, position)


}
