package viper.silicon.logger

import spray.json._

case class LogConfig(isBlackList: Boolean,
                     includeStore: Boolean, includeHeap: Boolean, includeOldHeap: Boolean, includePcs: Boolean,
                     recordConfigs: List[RecordConfig])

object LogConfig {
  def default(): LogConfig = LogConfig(
    isBlackList = true,
    includeStore = false, includeHeap = false, includeOldHeap = false, includePcs = false,
    List())
}

case class RecordConfig(kind: String, value: Option[String])

object LogConfigProtocol extends DefaultJsonProtocol {

  // recordConfigFormat has to appear before logConfigFormat!
  implicit val recordConfigFormat = jsonFormat2(RecordConfig.apply)
  implicit val logConfigFormat = jsonFormat6(LogConfig.apply)
}
