// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package rpi.inference.learner

import com.typesafe.scalalogging.LazyLogging
import rpi.inference.context.Context
import rpi.inference._
import rpi.inference.learner.template._
import rpi.util.{Collections, SeqMap}
import rpi.util.ast.Expressions._
import viper.silver.ast

import java.util.concurrent.atomic.AtomicInteger
import scala.collection.mutable
import scala.collection.mutable.ListBuffer

class GuardEncoder(context: Context, templates: Seq[Template]) extends LazyLogging {
  /**
    * Type shortcut for an effective guard.
    *
    * The inner sequence represents a choice that is possible if all guards of the sequence evaluate to true. The outer
    * sequence represents that exactly one of the choices should be picked.
    */
  private type Effective = Seq[Seq[Guard]]

  /**
    * Type shortcut for the map containing all effective guards.
    */
  private type EffectiveMap = Map[ast.LocationAccess, Effective]

  /**
    * The maximal number of clauses that may be used for a guard.
    */
  @inline
  private def maxClauses: Int =
    context.configuration.maxClauses()

  /**
    * The map from predicate names to the corresponding predicate template.
    */
  private val predicates: Map[String, PredicateTemplate] =
    templates
      .flatMap {
        case template: PredicateTemplate =>
          logger.info(template.toString)
          Some(template.name -> template)
        case _ => None
      }
      .toMap

  /**
    * The choices appearing in the templates.
    */
  private val choices = {
    def collectChoices(expression: TemplateExpression): Seq[Choice] =
      expression match {
        case Conjunction(conjuncts) =>
          conjuncts.flatMap { conjunct => collectChoices(conjunct) }
        case choice@Choice(_, _, _, body) =>
          choice +: collectChoices(body)
        case Truncation(_, body) =>
          collectChoices(body)
        case _ => Seq.empty
      }

    templates.flatMap {
      case template: PredicateTemplate =>
        collectChoices(template.body)
      case _ =>
        Seq.empty
    }
  }

  /**
    * A map, mapping specification names to maps containing all effective guards.
    */
  private val guards: Map[String, EffectiveMap] = {
    // the buffer used to accumulate parts of effective guards
    val buffer: mutable.Buffer[(ast.LocationAccess, Seq[Guard])] = ListBuffer.empty

    /**
      * Processes the given template.
      *
      * @param template The template to process.
      * @param depth    The depth up to which to process templates.
      * @param view     The view mapping template parameters to their expression in the current context.
      * @param guards   The guards collected so far.
      */
    def processTemplate(template: PredicateTemplate, depth: Int, view: View = View.empty, guards: Seq[Guard] = Seq.empty): Unit =
      if (depth != 0) {
        // get and adapt atoms
        val atoms = template
          .atoms
          .map { atom => view.adapt(atom) }
        // process body
        val body = template.body
        processExpression(body, view, guards)(depth, atoms)
      }

    /**
      * Processes the given template expression.
      *
      * @param expression The template expression to process.
      * @param view       The view mapping template parameters to their expression in the current context.
      * @param guards     The guards collected so far.
      * @param depth      The implicitly passed depth up to which to process templates.
      * @param atoms      The implicitly passed atoms available in the current template.
      */
    def processExpression(expression: TemplateExpression, view: View, guards: Seq[Guard])
                         (implicit depth: Int, atoms: Seq[ast.Exp]): Unit =
      expression match {
        case Conjunction(conjuncts) =>
          conjuncts.foreach { conjunct => processExpression(conjunct, view, guards) }
        case Wrapped(expression) => expression match {
          case ast.FieldAccessPredicate(ast.FieldAccess(receiver, field), _) =>
            // add guards for field access
            val access = ast.FieldAccess(view.adapt(receiver), field)()
            buffer.append(access -> guards)
          case ast.PredicateAccessPredicate(ast.PredicateAccess(arguments, name), _) =>
            // add guards for predicate access
            val adaptedArguments = arguments.map { argument => view.adapt(argument) }
            val access = ast.PredicateAccess(adaptedArguments, name)()
            buffer.append(access -> guards)
            // recursively process templates
            val innerTemplate = predicates(name)
            val innerView = View.create(innerTemplate, adaptedArguments)
            processTemplate(innerTemplate, depth - 1, innerView, guards)
          case _ =>
            sys.error(s"Unexpected expression in template: $expression")
        }
        case Guarded(guardId, body) =>
          val resourceGuard = ResourceGuard(guardId, atoms)
          processExpression(body, view, guards :+ resourceGuard)
        case Choice(choiceId, variable, choices, body) =>
          choices
            .zipWithIndex
            .foreach { case (choice, index) =>
              val choiceGuard = ChoiceGuard(choiceId, index)
              val adaptedView = view.updated(variable.name, view.adapt(choice))
              processExpression(body, adaptedView, guards :+ choiceGuard)
            }
        case Truncation(condition, body) =>
          val truncationGuard = TruncationGuard(view.adapt(condition))
          processExpression(body, view, guards :+ truncationGuard)
      }

    // compute effective guards for all predicate templates
    templates
      .flatMap {
        case template: PredicateTemplate =>
          // process template
          buffer.clear()
          processTemplate(template, depth = 3)
          // create map from accesses to effective guards
          val map = buffer.foldLeft(Map.empty: EffectiveMap) {
            case (result, (access, guards)) =>
              SeqMap.add(result, access, guards)
          }
          // add map
          Some(template.name -> map)
        case _ =>
          None
      }
      .toMap
  }

  /**
    * The atomic integer used to generate unique names.
    */
  private val unique = new AtomicInteger

  /**
    * Returns the encoding of the given samples.
    *
    * @param samples The samples to encode.
    * @return The constraints representing the encodings of the samples.
    */
  def encodeSamples(samples: Seq[Sample]): Seq[ast.Exp] = {
    if (logger.underlying.isDebugEnabled) {
      // log effective guards
      logger.debug("effective guards:")
      guards.foreach { case (specification, map) =>
        logger.debug(s"  $specification:")
        map.foreach { case (location, effective) =>
          logger.debug(s"    $location:")
          effective.foreach { choice =>
            logger.debug(s"      ${choice.mkString(" &&")}")
          }
        }
      }
      logger.debug("encode samples:")
      samples.foreach { sample => logger.debug(sample.toString) }
    }

    // the buffer that accumulates constraints
    implicit val buffer: mutable.Buffer[ast.Exp] = ListBuffer.empty

    // encode samples
    samples.foreach { sample => encodeSample(sample) }

    // encode that only one option per choice can be picked
    choices.foreach {
      case Choice(choiceId, _, options, _) =>
        val variables = options
          .indices
          .map { index => ast.LocalVar(s"c_${choiceId}_$index", ast.Bool)() }
        addConstraint(exactlyOne(variables))
    }

    // return encoding
    buffer.toSeq
  }

  /**
    * Encodes the given sample.
    *
    * @param sample The sample to encode.
    * @param buffer The implicitly passed buffer that accumulates global constraints.
    */
  private def encodeSample(sample: Sample)(implicit buffer: mutable.Buffer[ast.Exp]): Unit =
    sample match {
      case PositiveSample(records) =>
        val encoding = encodeRecords(records, default = false)
        addConstraint(encoding)
      case NegativeSample(record) =>
        val encoding = encodeRecord(record, default = false)
        addConstraint(makeNot(encoding))
      case ImplicationSample(leftRecord, rightRecords) =>
        val leftEncoding = encodeRecord(leftRecord, default = true)
        val rightEncoding = encodeRecords(rightRecords, default = false)
        addConstraint(makeImplication(leftEncoding, rightEncoding))
    }

  /**
    * Encodes the given records.
    *
    * @param records The records to encode.
    * @param default The default value used to approximate unknown atoms.
    * @param buffer  The implicitly passed buffer that accumulates global constraints.
    * @return The encoding.
    */
  private def encodeRecords(records: Seq[Record], default: Boolean)(implicit buffer: mutable.Buffer[ast.Exp]): ast.Exp = {
    /**
      * The given encodings are assumed to correspond to a sequence of records , where the record alternate between
      * inhaled and exhaled records (with odd length, starting and ending with inhaled records). The encoding produced
      * by this helper method capture the fact that permissions from an inhaled record only survive if it is not exhaled
      * by any onf the subsequent exhaled records.
      *
      * @param encodings The encodings corresponding to the records.
      * @return The resulting encoding.
      */
    def ensureFraming(encodings: Seq[ast.Exp]): (ast.Exp, ast.Exp) =
      encodings match {
        case inhaled +: exhaled +: rest =>
          val (restEncoding, restCondition) = ensureFraming(rest)
          val condition = makeAnd(makeNot(exhaled), restCondition)
          val encoding = makeOr(makeAnd(inhaled, condition), restEncoding)
          (encoding, condition)
        case Seq(inhaled) => (inhaled, makeTrue)
      }

    // compute encodings for records
    val encodings = records
      .zipWithIndex
      .map { case (record, index) =>
        // note: every other record is in negative position
        val adaptedDefault = if (index % 2 == 0) default else !default
        encodeRecord(record, adaptedDefault)
      }

    // encode framing constraints
    val (framed, _) = ensureFraming(encodings)
    framed
  }

  /**
    * Encodes the given record.
    *
    * @param record  The record to encode.
    * @param default The default value used to approximate unknown atoms.
    * @param buffer  The implicitly passed buffer that accumulates global constraints.
    * @return The encoding.
    */
  private def encodeRecord(record: Record, default: Boolean)(implicit buffer: mutable.Buffer[ast.Exp]): ast.Exp = {
    // get guards
    val name = record.specification.name
    val localGuards = guards.getOrElse(name, Map.empty)

    // compute encodings for location options
    val options = record
      .locations
      .flatMap { location =>
        // get guard and build encoding for location option
        val locationGuard = localGuards.getOrElse(location, Seq.empty)
        locationGuard.map { sequence =>
          // build encodings for option
          val conjuncts = sequence.map {
            case ResourceGuard(id, atoms) =>
              val values = record.abstraction.values(atoms)
              encodeState(id, values, default)
            case ChoiceGuard(choiceId, index) =>
              encodeChoice(choiceId, index)
            case TruncationGuard(condition) =>
              val value = record.abstraction.value(condition)
              value match {
                case Some(true) => makeTrue
                case Some(false) => makeFalse
                case _ =>
                  // TODO: Maybe try model evaluation here?
                  logger.info("shit happens")
                  ???
                  makeLiteral(default)
              }
          }
          // introduce auxiliary variable for location option
          val option = makeAnd(conjuncts)
          auxiliary(option)
        }
      }

    // it is never good to pick more than one option
    addConstraint(atMostOne(options))
    // at least one option needs to be picked
    auxiliary(makeOr(options))
  }

  /**
    * Computes the encoding of an abstract state defined by the given values for the guard with the given id.
    *
    * @param guardId The id of the guard.
    * @param values  The values defining the state.
    * @param default The default value to assume for unknown atoms (approximation).
    * @return The encoding.
    */
  private def encodeState(guardId: Int, values: Seq[Option[Boolean]], default: Boolean): ast.Exp = {
    // encode clauses
    val clauses = for (j <- 0 until maxClauses) yield {
      val clauseActivation = makeBoolean(s"x_${guardId}_$j")
      val clauseEncoding = {
        // encode literals
        val literals = values
          .zipWithIndex
          .map { case (value, i) =>
            val literalActivation = makeBoolean(s"y_${guardId}_${i}_$j")
            val literalEncoding = value match {
              case Some(sign) =>
                val variable = makeBoolean(s"s_${guardId}_${i}_$j")
                if (sign) variable else makeNot(variable)
              case None =>
                makeLiteral(default)
            }
            makeImplication(literalActivation, literalEncoding)
          }
        // conjoin all literals
        makeAnd(literals)
      }
      makeAnd(clauseActivation, clauseEncoding)
    }
    // return disjunction of clauses
    makeOr(clauses)
  }

  /**
    * Computes the encoding of the fact that the choice with the given id happens to be the option with the given index.
    *
    * @param choiceId The id of the choice.
    * @param index    The index of the option.
    * @return The encoding.
    */
  private def encodeChoice(choiceId: Int, index: Int): ast.Exp =
    makeBoolean(s"c_${choiceId}_$index")

  /**
    * Introduces an auxiliary variable for the given expression.
    *
    * @param expression The expression.
    * @param buffer     The implicitly passed buffer that accumulates global constraints.
    * @return The auxiliary variable.
    */
  private def auxiliary(expression: ast.Exp)(implicit buffer: mutable.Buffer[ast.Exp]): ast.LocalVar = {
    // create auxiliary variable
    val variable = makeBoolean(s"t_${unique.getAndIncrement}")
    // add equality constraint and return variable
    addConstraint(makeEquality(variable, expression))
    variable
  }

  /**
    * Adds the given expression to the list of constraints.
    *
    * @param expression The expression.
    * @param buffer     The implicitly passed buffer that accumulates global constraints.
    */
  private def addConstraint(expression: ast.Exp)(implicit buffer: mutable.Buffer[ast.Exp]): Unit =
    buffer.append(expression)

  /**
    * Computes the encoding of the fact that exactly one of the given expressions is true.
    *
    * @param expressions The expressions.
    * @return The encoding.
    */
  private def exactlyOne(expressions: Iterable[ast.Exp]): ast.Exp =
    makeAnd(makeOr(expressions), atMostOne(expressions))

  /**
    * Computes the encoding of the fact that at most one of the given expressions is true.
    *
    * @param expressions The expressions.
    * @return The encoding.
    */
  private def atMostOne(expressions: Iterable[ast.Exp]): ast.Exp = {
    val constraints = Collections
      .pairs(expressions)
      .map { case (first, second) => makeNot(makeAnd(first, second)) }
    makeAnd(constraints)
  }

  sealed trait Guard

  case class ResourceGuard(guardId: Int, atoms: Seq[ast.Exp]) extends Guard {
    override def toString: String = s"phi_$guardId[${atoms.mkString(", ")}]"
  }

  case class ChoiceGuard(choiceId: Int, index: Int) extends Guard {
    override def toString: String = s"c_$choiceId=$index"
  }

  case class TruncationGuard(condition: ast.Exp) extends Guard {
    override def toString: String = condition.toString()
  }

  object View {
    /**
      * Returns the empty view that does not assign any expression to any variable.
      *
      * @return The empty view.
      */
    def empty: View =
      View(Map.empty)

    /**
      * Creates the view for the given template with the given arguments.
      *
      * @param template  The template.
      * @param arguments The arguments.
      * @return The view.
      */
    def create(template: Template, arguments: Seq[ast.Exp]): View = {
      val names = template
        .specification
        .parameters
        .map { parameter => parameter.name }
      View(names.zip(arguments).toMap)
    }
  }

  /**
    * A view mapping variable names to the expressions with which they are instantiated.
    *
    * @param map The map.
    */
  case class View(map: Map[String, ast.Exp]) {
    /**
      * Returns whether the view is empty.
      *
      * @return True if the view is empty.
      */
    def isEmpty: Boolean = map.isEmpty

    /**
      * Adapt the expression according to the view.
      *
      * @param expression The expression to adapt.
      * @return The adapted expression.
      */
    def adapt(expression: ast.Exp): ast.Exp =
      if (isEmpty) expression
      else expression.transform {
        case variable@ast.LocalVar(name, _) =>
          map.getOrElse(name, variable)
      }

    /**
      * Updates the view by mapping the variable with the given name to the given expression.
      *
      * @param name       The name of the variable.
      * @param expression The expression.
      * @return The updated view.
      */
    def updated(name: String, expression: ast.Exp): View =
      View(map.updated(name, expression))
  }

}
