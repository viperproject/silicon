/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.tests

import java.nio.file.Path
import viper.silver.testing.SilSuite
import viper.silver.verifier.Verifier
import viper.silicon.{Silicon, SiliconFrontend}

class SiliconTests extends SilSuite {
  private val siliconTestDirectories = List("consistency")
  private val silTestDirectories = List("all", "quantifiedpermissions", "wands")

  override def testDirectories = siliconTestDirectories ++ silTestDirectories

  override def frontend(verifier: Verifier, files: Seq[Path]) = {
    require(files.length == 1, "tests should consist of exactly one file")

    val fe = new SiliconFrontend()
    fe.init(verifier)
    fe.reset(files.head)
    fe
  }

  lazy val verifiers = List(createSiliconInstance())

  private def createSiliconInstance() = {
    val args = Silicon.optionsFromScalaTestConfigMap(prefixSpecificConfigMap.getOrElse("silicon", Map()))
    val debugInfo = ("startedBy" -> "viper.silicon.SiliconTests") :: Nil
    val silicon = Silicon.fromPartialCommandLineArguments(args, debugInfo)

    silicon
  }
}
