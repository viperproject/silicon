// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2025 ETH Zurich.

package viper.silicon.tests

import viper.silicon.Silicon
import viper.silver.testing.{AbstractOutput, CounterexampleVariablesTests, CustomAnnotation, ExpectedCounterexample, OutputAnnotationId, SilOutput, TestCustomError, TestError}
import viper.silicon.interfaces.SiliconVariableCounterexample
import viper.silver.parser.{PBinExp, PBoolLit, PExp, PIdnUseExp, PIntLit, PSymOp, PUnExp}
import viper.silver.verifier.{ConstantEntry, FailureContext, Model, ModelEntry, VerificationError}

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
      case Some(silCounterexample: SiliconVariableCounterexample) => meetsExpectations(expectedCounterexample, silCounterexample.model)
      case _ => false
    }

  /** returns true if model2 contains at least the content expressed by model1 */
  def meetsExpectations(model1: ExpectedCounterexample, model2: Model): Boolean = {
    model1.exprs.forall {
      case PBinExp(lhs, r, rhs) if r.rs == PSymOp.EqEq => containsEquality(lhs, rhs, model2)
    }
  }

  def containsEquality(lhs: PExp, rhs: PExp, model: Model): Boolean =
    resolve(Vector(lhs, rhs), model).exists { case Vector(resolvedLhs, resolvedRhs) =>
      areEqualEntries(resolvedLhs, resolvedRhs) }

  /** resolves `expr` to a model entry in the given model. In case it's a field access, the corresponding permissions are returned as well */
  def resolve(expr: PExp, model: Model): Option[ModelEntry] = expr match {
    case PIntLit(value) => Some(ConstantEntry(value.toString()))
    case PBoolLit(value) => Some(ConstantEntry(value.rs.keyword))
    case PUnExp(r, PIntLit(value)) if r.rs == PSymOp.Neg => Some(ConstantEntry((-value).toString()))
    case idnuse: PIdnUseExp => model.entries.get(idnuse.name)
  }

  def resolve(exprs: Vector[PExp], model: Model): Option[Vector[ModelEntry]] = {
    val entries = exprs.map(expr => resolve(expr, model)).collect{ case Some(entry) => entry }
    if (exprs.size == entries.size) Some(entries) else None
  }

  def areEqualEntries(entry1: ModelEntry, entry2: ModelEntry): Boolean = (entry1, entry2) match {
    case (ConstantEntry(value1), ConstantEntry(value2)) => value1 == value2
  }

  override def notFoundError: TestError = TestCustomError(s"Expected the following counterexample on line $forLineNr: $expectedCounterexample")

  override def withForLineNr(line: Int = forLineNr): ExpectedValuesCounterexampleAnnotation = ExpectedValuesCounterexampleAnnotation(id, file, line, expectedCounterexample)
}
