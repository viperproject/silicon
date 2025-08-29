// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2025 ETH Zurich.

package viper.silicon.tests

import viper.silicon.Silicon
import viper.silver.testing.{AbstractOutput, CustomAnnotation, DefaultAnnotatedTestInput, DefaultTestInput, OutputAnnotationId, SilOutput, TestAnnotation, TestAnnotationParser, TestCustomError, TestError, TestInput}
import fastparse._
import viper.silicon.reporting.{ExtendedCounterexample, LitIntEntry, LitPermEntry, NullRefEntry, RecursiveRefEntry, RefEntry, SeqEntry}
import viper.silver.ast
import viper.silver.parser.FastParserCompanion.whitespace
import viper.silver.parser.{FastParser, PAccPred, PBinExp, PExp, PFieldAccess, PIdnUse, PIdnUseExp, PIntLit, PLookup, PSymOp, PUnExp}
import viper.silver.verifier.{ApplicationEntry, CESequence, CEValue, CEValueOnly, CEVariable, ConstantEntry, FailureContext, FieldFinalEntry, Rational, VerificationError}

import java.nio.file.Path

class GeneralCounterexampleTests extends SiliconTests {
  override val testDirectories: Seq[String] = Seq("counterexamples")

  override def configureVerifiersFromConfigMap(configMap: Map[String, Any]): Unit = {
    val args = Silicon.optionsFromScalaTestConfigMap(prefixSpecificConfigMap(configMap).getOrElse("silicon", Map()))
    val additionalArgs = Seq("--counterexample", "extended")

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
      case Some(ce: ExtendedCounterexample) => meetsExpectations(expectedCounterexample, ce)
      case _ => false
    }

  /** returns true if model2 contains at least the content expressed by model1 */
  def meetsExpectations(model1: ExpectedCounterexample, model2: ExtendedCounterexample): Boolean = {
    model1.exprs.forall {
      case accPred: PAccPred => containsAccessPredicate(accPred, model2)
      case PBinExp(lhs, r, rhs) if r.rs == PSymOp.EqEq => containsEquality(lhs, rhs, model2)
    }
  }

  def containsAccessPredicate(accPred: PAccPred, model: ExtendedCounterexample): Boolean = {
    resolve(Vector(accPred.loc, accPred.perm), model).exists {
      case Vector((_, actualPermOpt), (expectedPermAmount, _)) =>
        actualPermOpt.exists(actualPermAmount =>
          areEqualEntries(expectedPermAmount,
            CEValueOnly(ApplicationEntry("/", Seq(ConstantEntry(actualPermAmount.numerator.toString()), ConstantEntry(actualPermAmount.denominator.toString()))), Some(ast.Perm)))
        )
    }
  }

  def containsEquality(lhs: PExp, rhs: PExp, model: ExtendedCounterexample): Boolean =
    resolveWoPerm(Vector(lhs, rhs), model).exists { case Vector(resolvedLhs, resolvedRhs) =>
      areEqualEntries(resolvedLhs, resolvedRhs) }

  /** resolves `expr` to a model entry in the given model. In case it's a field access, the corresponding permissions are returned as well */
  def resolve(expr: PExp, model: ExtendedCounterexample): Option[(CEValue, Option[Rational])] = expr match {
    case PIntLit(value) => Some(CEValueOnly(ConstantEntry(value.toString()), Some(viper.silver.ast.Int)), None)
    case PUnExp(r, PIntLit(value)) if r.rs == PSymOp.Neg => Some(CEValueOnly(ApplicationEntry("-", Seq(ConstantEntry(value.toString()))), Some(ast.Int)), None)
    case PBinExp(PIntLit(n), r, PIntLit(d)) if r.rs == PSymOp.Div =>
      Some(CEValueOnly(ApplicationEntry("/", Seq(ConstantEntry(n.toString()), ConstantEntry(d.toString()))), Some(ast.Perm)), None)
    case idnuse: PIdnUseExp =>
      model.ceStore.asMap.get(idnuse.name).map((_, None))
    case PFieldAccess(rcv, _, idnuse) =>
      val rcvValue = resolveWoPerm(rcv, model)
      rcvValue.flatMap {
        case CEVariable(name, entry, _) => model.heaps.get("current").flatMap(_.heapEntries.find({
          case (f: ast.Field, ffi: FieldFinalEntry) if f.name == idnuse.name && (ffi.ref == name || ffi.ref == entry.toString) => true
          case _ => false
        }).map(he =>
          (he._2.asInstanceOf[FieldFinalEntry].entry, he._2.asInstanceOf[FieldFinalEntry].perm)
        ))
    }
    case PLookup(base, _, idx, _) => resolveWoPerm(Vector(base, idx), model).flatMap {
      case Vector(s: CESequence, CEValueOnly(ConstantEntry(i), _)) =>
        try {
          val evaluatedIdx = BigInt(i)
          val elemTyp = s.valueType match {
            case Some(ast.SeqType(memberType)) => Some(memberType)
            case _ => None
          }
          if (evaluatedIdx >= 0 && evaluatedIdx < s.length)
            Some((CEValueOnly(ConstantEntry(s.entries(evaluatedIdx)), elemTyp), None))
          else
            None
        } catch {
          case _: NumberFormatException => None
        }

    }
  }

  def resolve(exprs: Vector[PExp], model: ExtendedCounterexample): Option[Vector[(CEValue, Option[Rational])]] = {
    val entries = exprs.map(expr => resolve(expr, model)).collect{ case Some(entry) => entry }
    if (exprs.size == entries.size) Some(entries) else None
  }

  def resolveWoPerm(expr: PExp, model: ExtendedCounterexample): Option[CEValue] =
    resolve(expr, model).map(_._1)

  def resolveWoPerm(exprs: Vector[PExp], model: ExtendedCounterexample): Option[Vector[CEValue]] = {
    val entries = exprs.map(expr => resolveWoPerm(expr, model)).collect{ case Some(entry) => entry }
    if (exprs.size == entries.size) Some(entries) else None
  }

  def areEqualEntries(entry1: CEValue, entry2: CEValue): Boolean = (entry1, entry2) match {
    case (CEValueOnly(value1, _), CEValueOnly(value2, _)) => value1 == value2
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
