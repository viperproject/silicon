// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.logger.records

import viper.silicon.logger.LogConfig

import scala.annotation.unused

trait SymbolicRecord {
  var id: Int = -1

  override def toString: String = {
    s"$toTypeString $toSimpleString"
  }

  def toTypeString: String

  def toSimpleString: String

  def getData(@unused config: LogConfig): RecordData = {
    new RecordData()
  }
}
