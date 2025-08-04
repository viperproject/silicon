// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2025 ETH Zurich.

package viper.silicon.optimizations

import viper.silicon.verifier.Verifier
import scala.io.Source

object ProofEssence {

  val globalGuardName = "$GlobalGuard"

  def branchGuards(name: String, branch: String): List[String] = {
    val coreCacheFile = new java.io.File(s"${Verifier.config.tempDirectory()}/${name}_unsatCoreCache.cache")
    val cacheMap: Map[String, String] = {
      val source = Source.fromFile(coreCacheFile)
      try {
        source.getLines().collect {
          case line if line.contains(":") =>
            val Array(hash, core) = line.split(":", 2)
            hash -> core
        }.toMap
      } finally source.close()
    }
    val cores = cacheMap.get(branch) match {
      case Some(coresStr) =>
        val pattern = """\(([^)]*)\)""".r
        pattern.findAllMatchIn(coresStr).map(_.group(1)).toList
      case None => Nil
    }
    println(s"Cores = $cores")
    cores
  }
}

