package rpi.learner

import java.util.concurrent.atomic.AtomicInteger
import rpi.{Names, Settings}
import rpi.inference._
import rpi.util.{Collections, Expressions, SeqMap}
import viper.silver.ast

import scala.collection.mutable
import scala.collection.mutable.ListBuffer

class GuardEncoder(templates: Map[String, Template]) {

  import Expressions._

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
    * The choices appearing in the templates.
    */
  private val choices = {
    def collectChoices(expression: TemplateExpression): Seq[Choice] =
      expression match {
        case Conjunction(conjuncts) =>
          conjuncts.flatMap { conjunct => collectChoices(conjunct) }
        case choice@Choice(_, _, body) =>
          choice +: collectChoices(body)
        case Truncation(_, body) =>
          collectChoices(body)
        case _ => Seq.empty
      }

    templates.flatMap { case (_, template) => collectChoices(template.body) }
  }

  /**
    * A map, mapping specification names to maps containing all effective guards.
    */
  private val guards: Map[String, EffectiveMap] = {
    def collectGuards(template: Template, view: View, depth: Int): Map[ast.LocationAccess, Effective] =
      if (depth == 0) Map.empty
      else {
        // get and adapt atoms
        val atoms = template
          .atoms
          .map { atom => view.adapt(atom) }

        def collect(expression: TemplateExpression, result: Map[ast.LocationAccess, Effective], view: View): Map[ast.LocationAccess, Effective] =
          expression match {
            case Conjunction(conjuncts) =>
              conjuncts.foldLeft(result) {
                case (current, conjunct) => collect(conjunct, current, view)
              }
            case Guarded(guardId, access) =>
              val resourceGuard = ResourceGuard(guardId, atoms)
              access match {
                case ast.FieldAccess(receiver, field) =>
                  // update guard of field access
                  val adapted = ast.FieldAccess(view.adapt(receiver), field)()
                  SeqMap.add(result, adapted, Seq(resourceGuard))
                case ast.PredicateAccess(arguments, name) =>
                  // update guard of predicate access
                  val adaptedArguments = arguments.map { argument => view.adapt(argument) }
                  val adapted = ast.PredicateAccess(adaptedArguments, name)()
                  val updatedResult = SeqMap.add(result, adapted, Seq(resourceGuard))
                  // recursively collect guards
                  val innerTemplate = templates(name)
                  val innerView = View.create(innerTemplate, adaptedArguments)
                  collectGuards(innerTemplate, innerView, depth - 1)
                    .foldLeft(updatedResult) {
                      case (innerResult, (innerAccess, innerGuard)) =>
                        val updatedGuard = innerGuard.map { choice => choice :+ resourceGuard }
                        SeqMap.addAll(innerResult, innerAccess, updatedGuard)
                    }
              }
            case Choice(choiceId, choices, body) =>
              choices
                .zipWithIndex
                .foldLeft(result) {
                  case (currentResult, (choice, index)) =>
                    val choiceGuard = ChoiceGuard(choiceId, index)
                    val adaptedChoice = view.adapt(choice)
                    val innerView = view.updated(name = s"t_$choiceId", adaptedChoice)
                    collect(body, Map.empty, innerView)
                      .foldLeft(currentResult) {
                        case (innerResult, (innerAccess, innerGuard)) =>
                          val updatedGuard = innerGuard.map { choice => choice :+ choiceGuard }
                          SeqMap.addAll(innerResult, innerAccess, updatedGuard)
                      }
                }
            case Truncation(condition, body) =>
              val adaptedCondition = view.adapt(condition)
              val truncationGuard = TruncationGuard(adaptedCondition)
              collect(body, Map.empty, view)
                .foldLeft(result) {
                  case (innerResult, (innerAccess, innerGuard)) =>
                    val updatedGuard = innerGuard.map { choice => choice :+ truncationGuard }
                    SeqMap.addAll(innerResult, innerAccess, updatedGuard)
                }
          }

        // collect guards
        collect(template.body, Map.empty, view)
      }

    // collect effective guards for every template
    templates.flatMap { case (name, template) =>
      println(template)
      if (!Names.isPredicate(name)) {
        val map = collectGuards(template, View.empty, depth = 3)
        map.foreach { case (loc, g) =>
          println(s"  $loc:")
          g.foreach { x =>
            print("    ")
            println(x.mkString("(", " && ", ")"))
          }
        }
        Some(name -> map)
      } else None
    }
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
    // the buffer that accumulates constraints
    implicit val buffer: mutable.Buffer[ast.Exp] = ListBuffer.empty

    // encode samples
    samples.foreach { sample => encodeSample(sample) }

    // encode that only one option per choice can be picked
    choices.foreach {
      case Choice(choiceId, options, _) =>
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
        addConstraint(not(encoding))
      case ImplicationSample(leftRecord, rightRecords) =>
        val leftEncoding = encodeRecord(leftRecord, default = true)
        val rightEncoding = encodeRecords(rightRecords, default = false)
        addConstraint(implies(leftEncoding, rightEncoding))
    }

  /**
    * Encodes the given records.
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
          val condition = and(not(exhaled), restCondition)
          val encoding = or(and(inhaled, condition), restEncoding)
          (encoding, condition)
        case Seq(inhaled) => (inhaled, top)
      }

    // compute encodings for records
    val encodings = records
      .zipWithIndex
      .map { case (record, index) =>
        // note: every other record is in negative position
        val adapted = if (index % 2 == 0) default else !default
        encodeRecord(record, adapted)
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
              val values = record.abstraction.getValues(atoms)
              encodeState(id, values, default)
            case ChoiceGuard(choiceId, index) =>
              encodeChoice(choiceId, index)
            case TruncationGuard(condition) =>
              val value = record.abstraction.getValue(condition)
              value match {
                case Some(true) => top
                case Some(false) => bottom
                case _ =>
                  // TODO: Maybe try model evaluation here?
                  literal(default)
              }
          }
          // introduce auxiliary variable for location option
          val option = bigAnd(conjuncts)
          auxiliary(option)
        }
      }

    // it is never good to pick more than one option
    addConstraint(atMostOne(options))
    // at least one option needs to be picked
    auxiliary(bigOr(options))
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
    val clauses = for (j <- 0 until Settings.maxClauses) yield {
      val clauseActivation = ast.LocalVar(s"x_${guardId}_$j", ast.Bool)()
      val clauseEncoding = {
        // encode literals
        val literals = values
          .zipWithIndex
          .map { case (value, i) =>
            val literalActivation = ast.LocalVar(s"y_${guardId}_${i}_$j", ast.Bool)()
            val literalEncoding = value match {
              case Some(sign) =>
                val variable = ast.LocalVar(s"s_${guardId}_${i}_$j", ast.Bool)()
                if (sign) variable else not(variable)
              case None =>
                literal(default)
            }
            implies(literalActivation, literalEncoding)
          }
        // conjoin all literals
        bigAnd(literals)
      }
      and(clauseActivation, clauseEncoding)
    }
    // return disjunction of clauses
    bigOr(clauses)
  }

  /**
    * Computes the encoding of the fact that the choice with the given id happens to be the option with the given index.
    *
    * @param choiceId The id of the choice.
    * @param index    The index of the option.
    * @return The encoding.
    */
  private def encodeChoice(choiceId: Int, index: Int): ast.Exp =
    ast.LocalVar(s"c_${choiceId}_$index", ast.Bool)()

  /**
    * Introduces an auxiliary variable for the given expression.
    *
    * @param expression The expression.
    * @param buffer     The implicitly passed buffer that accumulates global constraints.
    * @return The auxiliary variable.
    */
  private def auxiliary(expression: ast.Exp)(implicit buffer: mutable.Buffer[ast.Exp]): ast.LocalVar = {
    // create auxiliary variable
    val name = s"t_${unique.getAndIncrement}"
    val variable = ast.LocalVar(name, ast.Bool)()
    // add equality constraint and return variable
    addConstraint(ast.EqCmp(variable, expression)())
    variable
  }

  /**
    * Adds the given expression to the list of constraints.
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
    and(bigOr(expressions), atMostOne(expressions))

  /**
    * Computes the encoding of the fact that at most one of the given expressions is true.
    *
    * @param expressions The expressions.
    * @return The encoding.
    */
  private def atMostOne(expressions: Iterable[ast.Exp]): ast.Exp = {
    val constraints = Collections
      .pairs(expressions)
      .map { case (first, second) => not(and(first, second)) }
    bigAnd(constraints)
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
    def empty: View =
      View(Map.empty)

    def create(template: Template, arguments: Seq[ast.Exp]): View = {
      val names = template
        .specification
        .parameters
        .map { parameter => parameter.name }
      View(names.zip(arguments).toMap)
    }
  }

  case class View(map: Map[String, ast.Exp]) {
    def isEmpty: Boolean = map.isEmpty

    def adapt(expression: ast.Exp): ast.Exp =
      if (isEmpty) expression
      else expression.transform {
        case variable@ast.LocalVar(name, _) =>
          map.getOrElse(name, variable)
      }

    def updated(name: String, value: ast.Exp): View =
      View(map.updated(name, value))
  }

}
