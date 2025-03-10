// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2022 ETH Zurich.

package viper.silicon.tests

import viper.silicon.Silicon
import viper.silver.testing.{AbstractOutput, CustomAnnotation, DefaultAnnotatedTestInput, DefaultTestInput, OutputAnnotationId, SilOutput, TestAnnotation, TestAnnotationParser, TestCustomError, TestError, TestInput}
import fastparse._
import viper.silicon.interfaces.SiliconMappedCounterexample
import viper.silicon.reporting.{ExtractedModel, ExtractedModelEntry, LitIntEntry, LitPermEntry, NullRefEntry, RecursiveRefEntry, RefEntry, SeqEntry}
import viper.silver.parser.FastParserCompanion.whitespace
import viper.silver.parser.{FastParser, PAccPred, PBinExp, PExp, PFieldAccess, PIdnUseExp, PIntLit, PLookup, PSymOp, PUnExp}
import viper.silver.utility.Common.Rational
import viper.silver.verifier.{FailureContext, VerificationError}

import java.nio.file.Path

class CounterexampleTests extends SiliconTests {
  override val testDirectories: Seq[String] = Seq("counterexamples")

  override def configureVerifiersFromConfigMap(configMap: Map[String, Any]): Unit = {
    val args = Silicon.optionsFromScalaTestConfigMap(prefixSpecificConfigMap(configMap).getOrElse("silicon", Map()))
    val additionalArgs = Seq("--counterexample", "mapped")

    silicon.parseCommandLine(args ++ additionalArgs :+ Silicon.dummyInputFilename)
  }

  override def buildTestInput(file: Path, prefix: String): DefaultAnnotatedTestInput =
    CounterexampleTestInput(file, prefix)

  /** we override the default annotation parser because we use special annotations to express expected counterexamples */
  object CounterexampleTestInput extends TestAnnotationParser {
    /**
      * Creates an annotated test input by parsing all annotations in the files
      * that belong to the given test input.
      */
    def apply(i: TestInput): DefaultAnnotatedTestInput =
      DefaultAnnotatedTestInput(i.name, i.prefix, i.files, i.tags,
        parseAnnotations(i.files))

    def apply(file: Path, prefix: String): DefaultAnnotatedTestInput =
      apply(DefaultTestInput(file, prefix))

    override def getAnnotationFinders: Seq[(String, Path, Int) => Option[TestAnnotation]] = {
      super.getAnnotationFinders :+ isExpectedCounterexample
    }

    // the use of comma is excluded from value ID (i.e. after the colon) to avoid ambiguities with the model
    // note that the second capturing group could be turned into a non-capturing group but this would break compatibility
    // with the parent trait
    override val outputIdPattern: String = "([^:]*)(:([^,]*))?"

    private def isExpectedCounterexample(annotation: String, file: Path, lineNr: Int): Option[TestAnnotation] = {
      def parseExpectedCounterexample(id: OutputAnnotationId, expectedCounterexampleString: String): Option[ExpectedCounterexampleAnnotation] = {
        // in order to reuse as much of the existing Viper parser as possible, we have to initialize the `_file` and `_line_offset` fields:
        val fp = new FastParser()
        fp._file = file.toAbsolutePath
        val lines = expectedCounterexampleString.linesWithSeparators
        fp._line_offset = (lines.map(_.length) ++ Seq(0)).toArray
        var offset = 0
        for (i <- fp._line_offset.indices) {
          val line_length = fp._line_offset(i)
          fp._line_offset(i) = offset
          offset += line_length
        }
        val cParser = new CounterexampleParser(fp)
        // now parsing is actually possible:
        fastparse.parse(expectedCounterexampleString, cParser.expectedCounterexample(_)) match {
          case Parsed.Success(expectedCounterexample, _) => Some(ExpectedCounterexampleAnnotation(id, file, lineNr, expectedCounterexample))
          case Parsed.Failure(_, _, extra) =>
            println(s"Parsing expected counterexample failed in file $file: ${extra.trace().longAggregateMsg}")
            None
        }
      }

      val regex = ("""^ExpectedCounterexample\(""" + outputIdPattern + """, (.*)\)$""").r
      annotation match {
        case regex(keyId, _, null, counterexample) =>
          parseExpectedCounterexample(OutputAnnotationId(keyId, None), counterexample)
        case regex(keyId, _, valueId, counterexample) =>
          parseExpectedCounterexample(OutputAnnotationId(keyId, Some(valueId)), counterexample)
        case _ => None
      }
    }
  }
}

/** represents an expected output (identified by `id`) with an associated (possibly partial) counterexample model */
case class ExpectedCounterexampleAnnotation(id: OutputAnnotationId, file: Path, forLineNr: Int, expectedCounterexample: ExpectedCounterexample) extends CustomAnnotation {
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
      case Some(silCounterexample: SiliconMappedCounterexample) => meetsExpectations(expectedCounterexample, silCounterexample.converter.extractedModel)
      case _ => false
    }

  /** returns true if model2 contains at least the content expressed by model1 */
  def meetsExpectations(model1: ExpectedCounterexample, model2: ExtractedModel): Boolean = {
    model1.exprs.forall {
      case accPred: PAccPred => containsAccessPredicate(accPred, model2)
      case PBinExp(lhs, r, rhs) if r.rs == PSymOp.EqEq => containsEquality(lhs, rhs, model2)
    }
  }

  def containsAccessPredicate(accPred: PAccPred, model: ExtractedModel): Boolean = {
    resolve(Vector(accPred.loc, accPred.perm), model).exists {
      case Vector((_, actualPermOpt), (expectedPermAmount, _)) =>
        actualPermOpt.exists(actualPermAmount => areEqualEntries(expectedPermAmount, LitPermEntry(actualPermAmount)))
    }
  }

  def containsEquality(lhs: PExp, rhs: PExp, model: ExtractedModel): Boolean =
    resolveWoPerm(Vector(lhs, rhs), model).exists { case Vector(resolvedLhs, resolvedRhs) =>
      areEqualEntries(resolvedLhs, resolvedRhs) }

  /** resolves `expr` to a model entry in the given model. In case it's a field access, the corresponding permissions are returned as well */
  def resolve(expr: PExp, model: ExtractedModel): Option[(ExtractedModelEntry, Option[Rational])] = expr match {
    case PIntLit(value) => Some(LitIntEntry(value), None)
    case PUnExp(r, PIntLit(value)) if r.rs == PSymOp.Neg => Some(LitIntEntry(-value), None)
    case PBinExp(PIntLit(n), r, PIntLit(d)) if r.rs == PSymOp.Div => Some(LitPermEntry(Rational(n, d)), None)
    case idnuse: PIdnUseExp => model.entries.get(idnuse.name).map((_, None))
    case PFieldAccess(rcv, _, idnuse) => resolveWoPerm(rcv, model).flatMap {
      case RefEntry(_, fields) => fields.get(idnuse.name)
    }
    case PLookup(base, _, idx, _) => resolveWoPerm(Vector(base, idx), model).flatMap {
      case Vector(SeqEntry(_, values), LitIntEntry(evaluatedIdx)) if values.size > evaluatedIdx => Some(values(evaluatedIdx.toInt), None)
    }
  }

  def resolve(exprs: Vector[PExp], model: ExtractedModel): Option[Vector[(ExtractedModelEntry, Option[Rational])]] = {
    val entries = exprs.map(expr => resolve(expr, model)).collect{ case Some(entry) => entry }
    if (exprs.size == entries.size) Some(entries) else None
  }

  def resolveWoPerm(expr: PExp, model: ExtractedModel): Option[ExtractedModelEntry] =
    resolve(expr, model).map(_._1)

  def resolveWoPerm(exprs: Vector[PExp], model: ExtractedModel): Option[Vector[ExtractedModelEntry]] = {
    val entries = exprs.map(expr => resolveWoPerm(expr, model)).collect{ case Some(entry) => entry }
    if (exprs.size == entries.size) Some(entries) else None
  }

  def areEqualEntries(entry1: ExtractedModelEntry, entry2: ExtractedModelEntry): Boolean = (entry1, entry2) match {
    case (LitIntEntry(value1), LitIntEntry(value2)) => value1 == value2
    case (LitPermEntry(value1), LitPermEntry(value2)) => value1 == value2
    case (RefEntry(name1, _), RefEntry(name2, _)) => name1 == name2
    case (RefEntry(name1, _), RecursiveRefEntry(name2)) => name1 == name2
    case (RecursiveRefEntry(name1), RefEntry(name2, _)) => name1 == name2
    case (NullRefEntry(name1), NullRefEntry(name2)) => name1 == name2
  }

  override def notFoundError: TestError = TestCustomError(s"Expected the following counterexample on line $forLineNr: $expectedCounterexample")

  override def withForLineNr(line: Int = forLineNr): ExpectedCounterexampleAnnotation = ExpectedCounterexampleAnnotation(id, file, line, expectedCounterexample)
}

/**
  * Simple input language to describe an expected counterexample with corresponding parser.
  * Currently, a counterexample is expressed by a comma separated list of access predicates and equalities (using the
  * same syntax as in Viper)
  */
class CounterexampleParser(fp: FastParser) {
  import fp.{accessPred, eqExp}

  def expectedCounterexample[_: P]: P[ExpectedCounterexample] =
    (Start ~ "(" ~ (accessPred | eqExp).rep(0, ",") ~ ")" ~ End)
      .map(ExpectedCounterexample)
}

case class ExpectedCounterexample(exprs: Seq[PExp]) {
  assert(exprs.forall {
    case _: PAccPred => true
    case PBinExp(_, r, _) if r.rs == PSymOp.EqEq => true
    case _ => false
  })
}
