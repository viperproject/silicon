// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.logger

import spray.json._
import viper.silicon.logger.records.data.DataRecord

case class LogConfig(isBlackList: Boolean,
                     includeStore: Boolean, includeHeap: Boolean, includeOldHeap: Boolean, includePcs: Boolean,
                     recordConfigs: List[RecordConfig]) {
  def getRecordConfig(d: DataRecord): Option[RecordConfig] = {
    for (rc <- recordConfigs) {
      if (rc.kind.equals(d.toTypeString)) {
        rc.value match {
          case Some(value) => if (value.equals(d.toSimpleString)) return Some(rc)
          case None => return Some(rc)
        }
      }
    }
    None
  }
}

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
