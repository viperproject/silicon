/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.tests

import java.nio.file.Path
import viper.silver.testing.{MissingOutput, UnexpectedOutput, LocatedAnnotation, SilSuite}
import viper.silver.verifier.{Verifier,AbstractError,Success => SilSuccess, Failure => SilFailure,
VerificationResult => SilVerificationResult}
import viper.silicon.{Silicon, SiliconFrontend}
import viper.silicon.SymbExLogger
import viper.silver.frontend.TranslatorState

class SiliconTests extends SilSuite {
  private val siliconTestDirectories = List("consistency")
  private val silTestDirectories = List("all", "quantifiedpermissions", "wands","examples", "quantifiedpredicates" ,"quantifiedcombinations")
  override def testDirectories = siliconTestDirectories ++ silTestDirectories

  override def frontend(verifier: Verifier, files: Seq[Path]) = {
    require(files.length == 1, "tests should consist of exactly one file")

    // For Unit-Testing of the Symbolic Execution Logging, the name of the file
    // to be tested must be known, which is why it's passed here to the SymbExLogger-Object.
    // SymbExLogger.reset() cleans the logging object (only relevant for verifying multiple
    // tests at once, e.g. with the 'test'-sbt-command.
    SymbExLogger.reset()
    SymbExLogger.filePath = files.head
    SymbExLogger.initUnitTestEngine()
    val fe = new SiliconFrontendWithUnitTesting()
    fe.init(verifier)
    fe.reset(files.head)
    fe
  }

  override def annotationShouldLeadToTestCancel(ann: LocatedAnnotation) = {
    ann match {
      case UnexpectedOutput(_, _, _, _, _, _) => true
      case MissingOutput(_, _, _, _, _, issue) =>
        issue != 34
      case _ => false
    }
  }

  lazy val verifiers = List(createSiliconInstance())

  private def createSiliconInstance() = {
    val args = Silicon.optionsFromScalaTestConfigMap(prefixSpecificConfigMap.getOrElse("silicon", Map()))
    val debugInfo = ("startedBy" -> "viper.silicon.SiliconTests") :: Nil
    val silicon = Silicon.fromPartialCommandLineArguments(args, debugInfo)

    silicon
  }
}

class SiliconFrontendWithUnitTesting extends SiliconFrontend {
  /** Is overridden only to append SymbExLogging-UnitTesting-Errors to the Result. **/
  override def result: SilVerificationResult = {
    if(_state < TranslatorState.Verified) super.result
    else{
      val symbExLogUnitTestErrors = SymbExLogger.unitTestEngine.verify()
      symbExLogUnitTestErrors match{
        case Nil => super.result
        case s1:Seq[AbstractError] => super.result match{
          case SilSuccess => SilFailure(s1)
          case SilFailure(s2) => SilFailure(s2 ++ s1)
        }
      }
    }
  }
}
