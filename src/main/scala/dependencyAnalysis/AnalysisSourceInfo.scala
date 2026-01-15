package viper.silicon.dependencyAnalysis

import viper.silver.ast
import viper.silver.ast._

object AnalysisSourceInfo {
  def extractPositionString(p: Position): String = {
    p match {
      case NoPosition => "???"
      case filePos: AbstractSourcePosition => filePos.file.getFileName.toString + " @ line " + filePos.line
      case lineColumn: HasLineColumn => "line " + lineColumn.line.toString
      case VirtualPosition(identifier) => "label " + identifier
    }
  }

  def createAnalysisSourceInfo(exp: ast.Exp): AnalysisSourceInfo = {
    val depInfo = exp.info.getUniqueInfo[FrontendDependencyAnalysisInfo]
    if(depInfo.isDefined) depInfo.get.createAnalysisSourceInfo()
    else ExpAnalysisSourceInfo(exp, exp.pos)
  }

  def createAnalysisSourceInfo(stmt: ast.Stmt): AnalysisSourceInfo = {
    val depInfo = stmt.info.getUniqueInfo[FrontendDependencyAnalysisInfo]
    if(depInfo.isDefined) depInfo.get.createAnalysisSourceInfo()
    else StmtAnalysisSourceInfo(stmt, stmt.pos)
  }

  def createAnalysisSourceInfo(description: String, pos: Position): AnalysisSourceInfo = StringAnalysisSourceInfo(description, pos)

}

abstract class AnalysisSourceInfo {
  override def toString: String = getPositionString

  def getDescription: String

  def getLineNumber: Option[Int] = getPosition match {
    case column: HasLineColumn => Some(column.line)
    case _ => None
  }

  def getPositionString: String = {
    AnalysisSourceInfo.extractPositionString(getPosition)
  }

  def getPosition: Position

  /**
   * @return the analysis source info used for lifting low-level graphs to higher-level graphs
   *         and presenting dependency results to the user
   */
  def getTopLevelSource: AnalysisSourceInfo = this

  /**
   * @return the analysis source info used for adding transitive edges within a source exp/stmt
   */
  def getSourceForTransitiveEdges: AnalysisSourceInfo = getTopLevelSource

  /**
   * @return the analysis source info used for joining graphs
   */
  def getFineGrainedSource: AnalysisSourceInfo = this

  def isAnalysisEnabled: Boolean = true
}

case class NoAnalysisSourceInfo() extends AnalysisSourceInfo {
  override def getPosition: Position = NoPosition

  override def getDescription: String = ""

  override def equals(obj: Any): Boolean = false
}

case class ExpAnalysisSourceInfo(source: ast.Exp, pos: Position) extends AnalysisSourceInfo {

  override def toString: String = getDescription + " (" + super.toString + ")"

  override def getPosition: Position = pos

  override def isAnalysisEnabled: Boolean = DependencyAnalyzer.extractEnableAnalysisFromInfo(source.info).getOrElse(true)

  override def getDescription: String = source.toString.replaceAll("\n", "\t")
}

case class StmtAnalysisSourceInfo(source: ast.Stmt, pos: Position) extends AnalysisSourceInfo {

  override def toString: String = getDescription + " (" + super.toString + ")"
  override def getPosition: Position = pos

  override def isAnalysisEnabled: Boolean = DependencyAnalyzer.extractEnableAnalysisFromInfo(source.info).getOrElse(true)

  override def getDescription: String = source.toString().replaceAll("\n", "\t")
}

case class StringAnalysisSourceInfo(description: String, position: Position) extends AnalysisSourceInfo {
  override def toString: String = getDescription + " (" + getPositionString + ")"
  override def getPosition: Position = position

  override def getDescription: String = description.replaceAll("\n", "\t")
}

case class TransitivityAnalysisSourceInfo(actualSource: AnalysisSourceInfo, transitivitySource: AnalysisSourceInfo) extends AnalysisSourceInfo {

  override def getPosition: Position = actualSource.getPosition
  override def toString: String = getTopLevelSource.toString

  override def getSourceForTransitiveEdges: AnalysisSourceInfo = transitivitySource.getTopLevelSource
  override def getTopLevelSource: AnalysisSourceInfo = actualSource.getTopLevelSource
  override def getFineGrainedSource: AnalysisSourceInfo = actualSource.getFineGrainedSource
  override def isAnalysisEnabled: Boolean = actualSource.isAnalysisEnabled

  override def getDescription: String = actualSource.getDescription
}

case class CompositeAnalysisSourceInfo(coarseGrainedSource: AnalysisSourceInfo, fineGrainedSource: AnalysisSourceInfo) extends AnalysisSourceInfo {
  override def toString: String = getTopLevelSource.toString
  override def getPosition: Position = coarseGrainedSource.getPosition

  override def getTopLevelSource: AnalysisSourceInfo = coarseGrainedSource.getTopLevelSource
  override def getFineGrainedSource: AnalysisSourceInfo = fineGrainedSource.getFineGrainedSource

  override def isAnalysisEnabled: Boolean = coarseGrainedSource.isAnalysisEnabled && fineGrainedSource.isAnalysisEnabled

  override def getDescription: String = coarseGrainedSource.getDescription
}
