package rpi.learner

import java.util.concurrent.atomic.AtomicInteger
import rpi.Settings
import rpi.inference._
import rpi.util.{Collections, Expressions, SeqMap}
import viper.silver.ast

class GuardEncoder(learner: Learner, templates: Map[String, Template]) {
  // import utility methods

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
            case Resource(guardId, access) =>
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
    templates.map { case (name, template) =>
      val map = collectGuards(template, View.empty, depth = 3)
      println(template)
      map.foreach { case (loc, g) =>
        println(s"  $loc:")
        g.foreach { x =>
          print("    ")
          println(x.mkString("(", " && ", ")"))
        }
      }
      name -> map
    }
  }

  /**
    * The atomic integer used to generate unique names.
    */
  private val unique = new AtomicInteger

  /**
    * Returns the encoding of the given examples.
    *
    * @param examples The examples to encode.
    * @return The constraints representing the encodings of the examples.
    */
  def encodeExamples(examples: Seq[Example]): Seq[ast.Exp] = {
    // encode examples
    val exampleEncodings = examples.flatMap { example => encodeExample(example) }
    // encode that only one option per choice can be picked
    val choiceEncodings = choices.map { case Choice(choiceId, options, _) =>
      val variables = options
        .indices
        .map { index => ast.LocalVar(s"c_${choiceId}_$index", ast.Bool)() }
      exactlyOne(variables)
    }
    // return encoding
    exampleEncodings ++ choiceEncodings
  }

  /**
    * Returns the encoding of the given example.
    *
    * @param example The example to encode.
    * @return The constraints representing the encoding of the example.
    */
  def encodeExample(example: Example): Seq[ast.Exp] =
    example match {
      case PositiveExample(records) =>
        val (encoding, constraints) = encodeRecords(records, default = false)
        constraints :+ encoding
      case NegativeExample(record) =>
        val (encoding, constraints) = encodeRecords(Seq(record), default = false)
        constraints :+ not(encoding)
      case ImplicationExample(leftRecord, rightRecords) =>
        val (leftEncoding, leftConstraints) = encodeRecords(Seq(leftRecord), default = true)
        val (rightEncoding, rightConstraints) = encodeRecords(rightRecords, default = false)
        leftConstraints ++ rightConstraints :+ implies(leftEncoding, rightEncoding)
    }

  /**
    * Encodes the given records.
    *
    * @param records The records to encode.
    * @param default The default value to assume for unknown atoms (approximation).
    * @return A tuple holding the encoding and a sequence of global constraints.
    */
  private def encodeRecords(records: Seq[Record], default: Boolean): (ast.Exp, Seq[ast.Exp]) = {
    // collect encodings and constraints
    // TODO: Fix default value (every other record is negative)
    val (variables, constraints) = {
      val empty = Seq.empty[ast.Exp]
      records.foldLeft((empty, empty)) {
        case ((variables, constraints), record) =>
          // get guards
          val name = record.specification.name
          val localGuards = guards.getOrElse(name, Map.empty)

          // compute encodings
          val encodings = record
            .locations
            .flatMap { location =>
              // get guard for location
              val locationGuard = localGuards.getOrElse(location, Seq.empty)
              // choices for this location
              locationGuard.map { sequence =>
                val conjuncts = sequence.map {
                  case ResourceGuard(id, atoms) =>
                    val values = record.abstraction.getValues(atoms)
                    encodeState(id, values, default)
                  case ChoiceGuard(choiceId, index) =>
                    encodeChoice(choiceId, index)
                  case TruncationGuard(condition) =>
                    val value = record.abstraction.getValue(condition)
                    value match {
                      case Some(true) => ast.TrueLit()()
                      case Some(false) => ast.FalseLit()()
                      case _ => ast.BoolLit(default)() // TODO: default.
                    }
                }
                Expressions.bigAnd(conjuncts)
              }
            }

          val (encodingVariables, equalities) = auxiliaries(encodings)
          val (variable, lower) = auxiliary(bigOr(encodingVariables))
          val upper = atMostOne(encodingVariables)
          (variables :+ variable, constraints ++ equalities :+ lower :+ upper)
      }
    }

    /**
      * The given encodings is assumed ot correspond to a sequence of records, where the records alternate between
      * inhaled records and exhaled records (starting and ending with inhaled records). The encoding produced by this
      * method captures that the permissions from an inhaled record only survive if it is not exhaled by any of the
      * subsequent exhaled records.
      *
      * @param encodings The encodings corresponding to the records.
      * @return The resulting encoding.
      */
    def ensureFraming(encodings: Seq[ast.Exp]): (ast.Exp, ast.Exp) =
      encodings match {
        case inhaled +: exhaled +: rest =>
          val (innerEncoding, innerCondition) = ensureFraming(rest)
          val condition = ast.And(ast.Not(exhaled)(), innerCondition)()
          val encoding = ast.Or(ast.And(inhaled, condition)(), innerEncoding)()
          (encoding, condition)
        case Seq(inhaled) => (inhaled, ast.TrueLit()())
      }

    // TODO: Remove conditional if list is never empty.
    val encoding =
      if (variables.isEmpty) ??? // was: true
      else ensureFraming(variables)._1

    (encoding, constraints)
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
                if (sign) variable else ast.Not(variable)()
              case None =>
                if (default) ast.TrueLit()() else ast.FalseLit()()
            }
            ast.Implies(literalActivation, literalEncoding)()
          }
        // conjoin all literals
        Expressions.bigAnd(literals)
      }
      ast.And(clauseActivation, clauseEncoding)()
    }
    // return disjunction of clauses
    Expressions.bigOr(clauses)
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

  // method used to introduce auxiliary variables
  private def auxiliary(expression: ast.Exp): (ast.LocalVar, ast.Exp) = {
    val name = s"t_${unique.getAndIncrement}"
    val variable = ast.LocalVar(name, ast.Bool)()
    val equality = ast.EqCmp(variable, expression)()
    (variable, equality)
  }

  // method used to introduce auxiliary variables.
  private def auxiliaries(expressions: Iterable[ast.Exp]): (Seq[ast.LocalVar], Seq[ast.Exp]) =
    expressions
      .foldLeft((Seq.empty[ast.LocalVar], Seq.empty[ast.Exp])) {
        case ((variables, equalities), expression) =>
          val (variable, equality) = auxiliary(expression)
          (variables :+ variable, equalities :+ equality)
      }

  /**
    * Computes the encoding of the fact that exactly one of the given expressions is true.
    *
    * @param expressions The expressions.
    * @return The encoding.
    */
  private def exactlyOne(expressions: Seq[ast.Exp]): ast.Exp = {
    ast.And(bigOr(expressions), atMostOne(expressions))()
  }

  /**
    * Computes the encoding of the fact that at most one of the given expressions is true.
    *
    * @param expressions The expressions.
    * @return The encoding.
    */
  private def atMostOne(expressions: Seq[ast.Exp]): ast.Exp = {
    val constraints = Collections
      .pairs(expressions)
      .map { case (first, second) =>
        ast.Not(ast.And(first, second)())()
      }
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
    override def toString: String = condition.toString
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
