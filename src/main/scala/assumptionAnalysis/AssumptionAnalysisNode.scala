package viper.silicon.assumptionAnalysis

import viper.silicon.assumptionAnalysis.AssumptionType.AssumptionType
import viper.silicon.interfaces.state.Chunk
import viper.silicon.state.terms.{False, Term, Var}
import viper.silver.ast


trait AssumptionAnalysisNode {
  val id: Int = AssumptionAnalysisGraphHelper.nextId()
  val sourceInfo: AnalysisSourceInfo
  val assumptionType: AssumptionType
  val isClosed: Boolean
  val term: Term
  val member: Option[ast.Member]
  def getTerm: Term = term

  override def toString: String = id.toString + " | " + getNodeString + " | " + sourceInfo.toString

  def getNodeString: String
  def getNodeType: String

  override def hashCode(): Int =
    toString.hashCode
}

trait GeneralAssumptionNode extends AssumptionAnalysisNode {
  override def getNodeType: String = "Assumption"
}
trait GeneralAssertionNode extends AssumptionAnalysisNode {
  override def getNodeType: String = "Assertion"
}

trait ChunkAnalysisInfo {
  val chunk: Chunk
  def getChunk: Chunk = chunk
}

case class SimpleAssumptionNode(term: Term, description: Option[String], sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType, isClosed: Boolean, member: Option[ast.Member]) extends GeneralAssumptionNode {
  override def getNodeString: String = "assume " + term.toString + description.map(" (" + _ + ")").getOrElse("")
}

case class AxiomAssumptionNode(term: Term, description: Option[String], sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType, isClosed: Boolean, member: Option[ast.Member]) extends GeneralAssumptionNode {
  override def getNodeString: String = "assume axiom " + term.toString + description.map(" (" + _ + ")").getOrElse("")
}

case class SimpleAssertionNode(term: Term, assumptionType: AssumptionType, sourceInfo: AnalysisSourceInfo, isClosed: Boolean, member: Option[ast.Member]) extends GeneralAssertionNode {
  override def getNodeString: String = "assert " + term.toString
}

case class SimpleCheckNode(term: Term, assumptionType: AssumptionType, sourceInfo: AnalysisSourceInfo, isClosed: Boolean, member: Option[ast.Member]) extends GeneralAssertionNode {
  override def getNodeString: String = "check " + term
  override def getNodeType: String = "Check"
}

case class PermissionInhaleNode(chunk: Chunk, term: Term, sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType, isClosed: Boolean, labelNode: LabelNode, member: Option[ast.Member]) extends GeneralAssumptionNode with ChunkAnalysisInfo {
  override def getNodeString: String = "inhale " + chunk.toString
  override def getNodeType: String = "Inhale"
}

case class PermissionExhaleNode(chunk: Chunk, term: Term, sourceInfo: AnalysisSourceInfo, assumptionType: AssumptionType, isClosed: Boolean, member: Option[ast.Member]) extends GeneralAssertionNode with ChunkAnalysisInfo {
  override def getNodeType: String = "Exhale"
  override def getNodeString: String = "exhale " + chunk.toString
}

case class LabelNode(term: Var, member: Option[ast.Member]) extends GeneralAssumptionNode() {
  val sourceInfo: AnalysisSourceInfo = NoAnalysisSourceInfo()
  val assumptionType: AssumptionType = AssumptionType.Internal
  val isClosed: Boolean = true
  val description: String = term.toString
  override def getNodeType: String = "Label"
  override def getNodeString: String = "assume " + description
}

case class InfeasibilityNode(sourceInfo: AnalysisSourceInfo, member: Option[ast.Member]) extends GeneralAssumptionNode {
  val term: Term = False
  val assumptionType: AssumptionType = AssumptionType.Implicit
  val isClosed: Boolean = true
  val description: String = "False"

  override def getNodeType: String = "Infeasible"
  override def getNodeString: String = "infeasible"
}
