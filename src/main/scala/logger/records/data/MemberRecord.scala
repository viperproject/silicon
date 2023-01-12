// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.logger.records.data

import viper.silicon.logger.LogConfig
import viper.silicon.logger.records.RecordData
import viper.silicon.state.terms.Term

trait MemberRecord extends DataRecord {
  var lastFailedProverQuery: Option[Term] = None

  override def getData(config: LogConfig): RecordData = {
    val data = super.getData(config)
    data.lastSMTQuery = lastFailedProverQuery
    data
  }
}
