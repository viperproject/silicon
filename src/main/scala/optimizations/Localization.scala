// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2025 ETH Zurich.

package viper.silicon.optimizations

import viper.silicon.verifier.Verifier
import scala.io.Source

object ProofEssence {
  // methodName -> (branchHash -> core, supercore, set of branch hashes in the supercore)
  private val cacheMapByName = scala.collection.mutable.Map.empty[String, (Map[String, String], String, Set[String])]

  val globalGuardName = "$GlobalGuard"
  val guardVariableName = "$LocalGuardVar"

  def branchGuards(name: String, branch: String): List[String] = {
    val coreCacheFile = new java.io.File(s"${Verifier.config.tempDirectory()}/${name}_unsatCoreCache.cache")
    val (coreMap, supercore, branchhashes) = cacheMapByName.getOrElseUpdate(name, {
      val source = Source.fromFile(coreCacheFile)
      try {
        val coreMap: Map[String, String] = source.getLines().collect {
          case line if line.contains(":") =>
            val Array(hash, core) = line.split(":", 2)
            hash -> core
        }.toMap
        (coreMap, "", Set(""))
      } finally source.close()
      val supercore = coreMap.values.fold(Set[String].empty)((a, b) => a.split(";").toSet() | b.split(";").toSet())
      val branchhashes = coreMap.keys.filter(hash => coreMap(hash).split(";").toSet()
    })
    val cores = coreMap.get(branch) match {
      case Some(coresStr) => coresStr.split(";").toList
      case None => Nil
    }
    cores
  }
}

