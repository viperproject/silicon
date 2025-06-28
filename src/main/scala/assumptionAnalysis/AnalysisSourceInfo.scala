package viper.silicon.assumptionAnalysis

import viper.silicon.verifier.Verifier
import viper.silver.ast
import viper.silver.ast._


abstract class AnalysisSourceInfo {
  override def toString: String = getStringForExport

  def getStringForExport: String = {
    getPosition match {
      case NoPosition => "???"
      case filePos: AbstractSourcePosition => filePos.file.getFileName.toString + " @ line " + filePos.line
      case column: HasLineColumn => "line " + column.line.toString
      case VirtualPosition(identifier) => "label " + identifier
    }
  }

  def getPosition: Position

  def getTopLevelSource: AnalysisSourceInfo = this

  def getFineGrainedSource: AnalysisSourceInfo = this

  def isAnalysisEnabled: Boolean = true
}

case class NoAnalysisSourceInfo() extends AnalysisSourceInfo {
  override def getPosition: Position = NoPosition
}

case class ExpAnalysisSourceInfo(source: ast.Exp) extends AnalysisSourceInfo {
  override def toString: String = (if(source.info.getSourceString.isEmpty) source.toString else source.info.getSourceString) +
    " (" + super.toString + ")"

  override def getPosition: Position = source.pos

  override def equals(obj: Any): Boolean = {
    obj match {
      case info: ExpAnalysisSourceInfo =>
        info.source.equals(this.source) && info.getPosition.equals(this.getPosition)
      case _ => false
    }
  }

  override def isAnalysisEnabled: Boolean = AssumptionAnalyzer.extractEnableAnalysisFromInfo(source.info).getOrElse(true)
}

case class StmtAnalysisSourceInfo(source: ast.Stmt) extends AnalysisSourceInfo {
  override def toString: String = (if(source.info.getSourceString.isEmpty) source.toString() else source.info.getSourceString) +
    " (" + super.toString + ")"
  override def getPosition: Position = source.pos

  override def equals(obj: Any): Boolean = {
    obj match {
      case info: StmtAnalysisSourceInfo =>
        info.source.equals(this.source) && info.getPosition.equals(this.getPosition)
      case _ => false
    }
  }

  override def isAnalysisEnabled: Boolean = AssumptionAnalyzer.extractEnableAnalysisFromInfo(source.info).getOrElse(true)
}

case class StringAnalysisSourceInfo(description: String, position: Position) extends AnalysisSourceInfo {
  override def toString: String = description + " (" + super.toString + ")"
  override def getPosition: Position = position
}

case class CompositeAnalysisSourceInfo(coarseGrainedSource: AnalysisSourceInfo, fineGrainedSource: AnalysisSourceInfo) extends AnalysisSourceInfo {
  override def toString: String = coarseGrainedSource.toString
  override def getPosition: Position = coarseGrainedSource.getPosition

  override def equals(obj: Any): Boolean = coarseGrainedSource.equals(obj)

  override def getTopLevelSource: AnalysisSourceInfo = coarseGrainedSource
  override def getFineGrainedSource: AnalysisSourceInfo = fineGrainedSource

  override def isAnalysisEnabled: Boolean = coarseGrainedSource.isAnalysisEnabled && fineGrainedSource.isAnalysisEnabled
}


case class AnalysisSourceInfoStack() {
  private var sourceInfos: List[AnalysisSourceInfo] = List.empty
  private var forcedMainSource: Option[AnalysisSourceInfo] = None

  def getAnalysisSourceInfos: List[AnalysisSourceInfo] = sourceInfos

  def getFullSourceInfo: AnalysisSourceInfo = {
    if(!Verifier.config.enableAssumptionAnalysis()) return NoAnalysisSourceInfo()
    if(forcedMainSource.isDefined)
      return forcedMainSource.get
    if(sourceInfos.size <= 1){
      sourceInfos.headOption.getOrElse(NoAnalysisSourceInfo())
    } else{
      CompositeAnalysisSourceInfo(sourceInfos.last, sourceInfos.head)
    }
  }

  def addAnalysisSourceInfo(analysisSourceInfo: AnalysisSourceInfo): Unit = {
    if(!Verifier.config.enableAssumptionAnalysis()) return
    sourceInfos = analysisSourceInfo +: sourceInfos
  }

  def setAnalysisSourceInfo(analysisSourceInfo: List[AnalysisSourceInfo]): Unit = {
    if(!Verifier.config.enableAssumptionAnalysis()) return
    sourceInfos = analysisSourceInfo
  }

  def popAnalysisSourceInfo(analysisSourceInfo: AnalysisSourceInfo): Unit = {
    if(!Verifier.config.enableAssumptionAnalysis()) return

    var currSourceInfo = sourceInfos
    // popping just one source info might not be enough since infeasible branches might return without popping the source info
    while(currSourceInfo.nonEmpty && !currSourceInfo.head.equals(analysisSourceInfo)) {
      currSourceInfo = currSourceInfo.tail
    }
    if(currSourceInfo.isEmpty || !currSourceInfo.head.equals(analysisSourceInfo))
      throw new RuntimeException("unexpected source info")
    sourceInfos = currSourceInfo.tail
  }

  def setForcedSource(description: String): Unit = {
    forcedMainSource = Some(StringAnalysisSourceInfo(description, getFullSourceInfo.getPosition))
  }

  def setForcedSource(source: AnalysisSourceInfo): Unit = {
    forcedMainSource = Some(source)
  }

  def removeForcedSource(): Unit = {
    forcedMainSource = None
  }
}