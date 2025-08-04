package viper.silicon.assumptionAnalysis

import viper.silicon.verifier.Verifier
import viper.silver.ast.NoPosition

trait SourceInfoStack {

  def getAnalysisSourceInfos: List[AnalysisSourceInfo]

  def getFullSourceInfo: AnalysisSourceInfo

  def addAnalysisSourceInfo(analysisSourceInfo: AnalysisSourceInfo): Unit

  def setAnalysisSourceInfo(analysisSourceInfo: List[AnalysisSourceInfo]): Unit

  def popAnalysisSourceInfo(analysisSourceInfo: AnalysisSourceInfo): Unit

  def getForcedSource: _root_.scala.Option[AnalysisSourceInfo]

  def setForcedSource(description: _root_.java.lang.String): Unit

  def setForcedSource(source: AnalysisSourceInfo): Unit

  def setForcedSource(sourceOpt: _root_.scala.Option[AnalysisSourceInfo]): Unit

  def removeForcedSource(): Unit
}

case class AnalysisSourceInfoStack() extends SourceInfoStack {
  private var sourceInfos: List[AnalysisSourceInfo] = List.empty
  private var forcedMainSource: Option[AnalysisSourceInfo] = None

  override def getAnalysisSourceInfos: List[AnalysisSourceInfo] = sourceInfos

  override def getFullSourceInfo: AnalysisSourceInfo = {
    if(!Verifier.config.enableAssumptionAnalysis()) return NoAnalysisSourceInfo()
    if(forcedMainSource.isDefined)
      return forcedMainSource.get
    if(sourceInfos.size <= 1){
      sourceInfos.headOption.getOrElse(NoAnalysisSourceInfo())
    } else{
      CompositeAnalysisSourceInfo(sourceInfos.last, sourceInfos.head)
    }
  }

  override def addAnalysisSourceInfo(analysisSourceInfo: AnalysisSourceInfo): Unit = {
    if(!Verifier.config.enableAssumptionAnalysis()) return
    sourceInfos = analysisSourceInfo +: sourceInfos
  }

  override def setAnalysisSourceInfo(analysisSourceInfo: List[AnalysisSourceInfo]): Unit = {
    if(!Verifier.config.enableAssumptionAnalysis()) return
    sourceInfos = analysisSourceInfo
  }

  override def popAnalysisSourceInfo(analysisSourceInfo: AnalysisSourceInfo): Unit = {
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

  override def getForcedSource: Option[AnalysisSourceInfo] = forcedMainSource

  override def setForcedSource(description: String): Unit = {
    forcedMainSource = Some(StringAnalysisSourceInfo(description, NoPosition))
  }

  override def setForcedSource(source: AnalysisSourceInfo): Unit = {
    forcedMainSource = Some(source)
  }

  override def setForcedSource(sourceOpt: Option[AnalysisSourceInfo]): Unit = {
    forcedMainSource = sourceOpt
  }

  override def removeForcedSource(): Unit = {
    forcedMainSource = None
  }
}