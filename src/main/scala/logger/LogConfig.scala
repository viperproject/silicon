// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

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
