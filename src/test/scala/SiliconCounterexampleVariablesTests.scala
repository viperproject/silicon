// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2025 ETH Zurich.

package viper.silicon.tests

import viper.silicon.Silicon
import viper.silver.testing.{AbstractOutput, CounterexampleComparison, CounterexampleVariablesTests, CustomAnnotation, ExpectedCounterexample, OutputAnnotationId, SilOutput, TestCustomError, TestError}
import viper.silicon.interfaces.SiliconVariableCounterexample
import viper.silver.verifier.{FailureContext, VerificationError}

import java.nio.file.Path

class SiliconCounterexampleVariablesTests extends SiliconTests with CounterexampleVariablesTests {

  override def configureVerifiersFromConfigMap(configMap: Map[String, Any]): Unit = {
    val args = Silicon.optionsFromScalaTestConfigMap(prefixSpecificConfigMap(configMap).getOrElse("silicon", Map()))
    val additionalArgs = Seq("--counterexample=variables", "--exhaleMode=1")

    silicon.parseCommandLine(args ++ additionalArgs :+ Silicon.dummyInputFilename)
  }

  override def createExpectedValuesCounterexampleAnnotation(id: OutputAnnotationId, file: Path, forLineNr: Int, expectedCounterexample: ExpectedCounterexample): CustomAnnotation =
    ExpectedValuesCounterexampleAnnotation(id, file, forLineNr, expectedCounterexample)
}

/** represents an expected output (identified by `id`) with an associated (possibly partial) counterexample model */
case class ExpectedValuesCounterexampleAnnotation(id: OutputAnnotationId, file: Path, forLineNr: Int, expectedCounterexample: ExpectedCounterexample) extends CustomAnnotation {
  override def matches(actual: AbstractOutput): Boolean =
    id.matches(actual.fullId) && actual.isSameLine(file, forLineNr) && containsModel(actual)

  /** returns true if the expected model (i.e. class parameter) is a subset of a model given in a failure context */
  def containsModel(is: AbstractOutput): Boolean = is match {
    case SilOutput(err) => err match {
      case vErr: VerificationError => vErr.failureContexts.toVector.exists(containsExpectedCounterexample)
      case _ => false
    }
    case _ => false
  }

  def containsExpectedCounterexample(failureContext: FailureContext): Boolean =
    failureContext.counterExample match {
      case Some(silCounterexample: SiliconVariableCounterexample) => CounterexampleComparison.meetsExpectations(expectedCounterexample, silCounterexample.model)
      case _ => false
    }

  override def notFoundError: TestError = TestCustomError(s"Expected the following counterexample on line $forLineNr: $expectedCounterexample")

  override def withForLineNr(line: Int = forLineNr): ExpectedValuesCounterexampleAnnotation = ExpectedValuesCounterexampleAnnotation(id, file, line, expectedCounterexample)
}
