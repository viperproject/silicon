/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon
package tests

import java.nio.file.Path
import silver.testing.SilSuite
import silver.verifier.Verifier

class SiliconTests extends SilSuite {
  private val siliconTestDirectories = List("consistency")
  private val silTestDirectories = List(/*"all,"*/ "fcts")

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
    val silicon = new Silicon(Seq(("startedBy", "viper.silicon.SiliconTests")))
    val args = optionsFromScalaTestConfigMap() ++ Seq("dummy.silver")

    silicon.parseCommandLine(args)

    silicon.config.initialize {
      case _ =>
        /* Ignore command-line errors, --help, --version and other non-positive
         * results from Scallop.
         * After initialized has been set to true, Silicon itself will not call
         * config.initialize again.
         */
        silicon.config.initialized = true
    }

    silicon
  }

  private def optionsFromScalaTestConfigMap(): Seq[String] = {
    val prefix = "silicon"

    prefixSpecificConfigMap.get(prefix) match {
      case None => Seq()
      case Some(optionMap) => optionMap.flatMap{
        case (k, v) => Seq(s"--$k", v.toString)
      }.toSeq
    }
  }
}
