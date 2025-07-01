// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2025 ETH Zurich.

package viper.silicon.optimizations

import viper.silicon.verifier.Verifier

object ProofEssence {
  def branchGuards(name: String, branch: String): List[String] = {
    val coreCacheFile = new java.io.File(s"${Verifier.config.tempDirectory()}/${name}_unsatCoreCache.cache")
  }
}

