// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2025 ETH Zurich.

package viper.silicon.optimizations

import viper.silicon.verifier.Verifier
import scala.io.Source

object ProofEssence {
  // methodName -> (supercore, set of branch hashes in the supercore, set of all branches found in the file)
  private val cacheMapByName = scala.collection.mutable.Map.empty[String, (List[String], Set[String], Set[String])]

  val globalGuardName = "$GlobalGuard"
  val guardVariableName = "$LocalGuardVar"

  /**
   * Retrieves the list of guard expressions for the given method and branch.
   *
   * @param name   the name of the method
   * @param branch the branch hash identifier
   * @return       a list of guard strings extracted from the cached unsat core
   */
  def branchGuards(name: String, branch: String): List[String] = {
    val coreCacheFile = new java.io.File(s"${Verifier.config.tempDirectory()}/${name}_unsatCoreCache.cache")
    if (!coreCacheFile.exists()) {
      List(globalGuardName)
    } else {
      val (supercore: List[String], branches: Set[String], allbranches: Set[String]) = cacheMapByName.getOrElseUpdate(name, {
        val source = Source.fromFile(coreCacheFile)
        try {
          val coreMap: Map[String, String] = source.getLines().collect {
            case line if line.contains(":") =>
              val Array(hash, core) = line.split(":", 2)
              hash -> core
          }.toMap
          val coresSorted = coreMap.toList.sortWith((a, b) => a._2.split(";").length < b._2.split(";").length)
          val (supercoreSet, branches) = coresSorted.foldLeft[(Set[String], Set[String])]((Set.empty, Set.empty))(
            (sofar, newcore) => {
              val coreset = newcore._2.split(";").toSet
              if (coreset subsetOf sofar._1) sofar
              else (coreset | sofar._1, sofar._2 + newcore._1)
            }
          )
          (supercoreSet.toList, branches, coreMap.keySet)
        } finally source.close()
      })
      val cores = if ((branches contains branch) || !(allbranches contains branch)) List(globalGuardName)
      else supercore
      cores.filter(_.length() > 0)
    }
  }
}

