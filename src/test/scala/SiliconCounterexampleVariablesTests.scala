// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2025 ETH Zurich.

package viper.silicon.tests

import viper.silicon.Silicon
import viper.silver.testing.{CounterexampleComparison, CounterexampleVariablesTests, ExpectedCounterexample, ExpectedValuesCounterexampleAnnotation, OutputAnnotationId, TestCustomError, TestError}
import viper.silicon.interfaces.SiliconVariableCounterexample
import viper.silver.verifier.FailureContext

import java.nio.file.Path

class SiliconCounterexampleVariablesTests extends SiliconTests with CounterexampleVariablesTests {

  override def configureVerifiersFromConfigMap(configMap: Map[String, Any]): Unit = {
    val args = Silicon.optionsFromScalaTestConfigMap(prefixSpecificConfigMap(configMap).getOrElse("silicon", Map()))
    val additionalArgs = Seq("--counterexample=variables", "--exhaleMode=1")

    silicon.parseCommandLine(args ++ additionalArgs :+ Silicon.dummyInputFilename)
  }

  override def createExpectedValuesCounterexampleAnnotation(id: OutputAnnotationId, file: Path, forLineNr: Int, expectedCounterexample: ExpectedCounterexample): ExpectedValuesCounterexampleAnnotation =
    SiliconExpectedValuesCounterexampleAnnotation(id, file, forLineNr, expectedCounterexample)
}

/** represents an expected output (identified by `id`) with an associated (possibly partial) counterexample model */
case class SiliconExpectedValuesCounterexampleAnnotation(id: OutputAnnotationId, file: Path, forLineNr: Int, expectedCounterexample: ExpectedCounterexample) extends
  ExpectedValuesCounterexampleAnnotation(id, file, forLineNr, expectedCounterexample) {

  def containsExpectedCounterexample(failureContext: FailureContext): Boolean =
    failureContext.counterExample match {
      case Some(silCounterexample: SiliconVariableCounterexample) => CounterexampleComparison.meetsExpectations(expectedCounterexample, silCounterexample.model)
      case _ => false
    }

  override def notFoundError: TestError = TestCustomError(s"Expected the following counterexample on line $forLineNr: $expectedCounterexample")

  override def withForLineNr(line: Int = forLineNr): ExpectedValuesCounterexampleAnnotation = SiliconExpectedValuesCounterexampleAnnotation(id, file, line, expectedCounterexample)
}
