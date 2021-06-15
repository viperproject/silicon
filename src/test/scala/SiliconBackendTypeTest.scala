// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

import viper.silicon.Silicon
import viper.silver.reporter.NoopReporter
import viper.silver.testing.BackendTypeTest
import viper.silver.verifier.Verifier

class SiliconBackendTypeTest extends BackendTypeTest {
  override val verifier: Verifier = {
    val reporter = NoopReporter
    val debugInfo = ("startedBy" -> "viper.silicon.SiliconSMTTypeTest") :: Nil
    new Silicon(reporter, debugInfo)
  }
}