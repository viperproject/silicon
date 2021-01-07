package rpi.learner

import java.util.concurrent.atomic.AtomicInteger

import rpi.Settings
import rpi.inference._
import rpi.util.{Collections, Expressions}
import viper.silver.ast

class GuardEncoder(learner: Learner, templates: Map[String, Template]) {
  // import utility methods

  import Expressions._

  /**
    * Type shortcut for an effective guard.
    *
    * The outer sequence represents a choice of exactly one of the options. The inner sequence represents a disjunction
    * of guards. The guards are represented by their id and which atomic predicates of the context correspond to the
    * atomic predicates of the guard.
    */
  private type Effective = Seq[Seq[(Int, Seq[ast.Exp])]]

  private val guards: Map[String, Map[ast.LocationAccess, Effective]] = {
    // compute effective guards.
    val result = templates
      .map { case (name, template) =>
        // TODO: Depth depending on length of longest access path.
        name -> collectGuards(template, View.empty, depth = 3)
      }

    // debug printing
    if (Settings.debugPrintGuards) result
      .foreach { case (name, map) => map
        .foreach { case (location, guard) =>
          val label = s"$location@$name"
          val string = guard
            .map { choice =>
              choice
                .map { case (id, atoms) =>
                  s"phi_$id${atoms.mkString("[", ",", "]")}"
                }
                .mkString(" && ")
            }
            .mkString("{", ", ", "}")
          println(s"$label: $string")
        }
      }

    // return effective guards
    result
  }

  private val unique = new AtomicInteger

  /**
    * Returns the encoding of the given examples.
    *
    * @param examples The examples to encode.
    * @return The constraints representing the encodings of the examples.
    */
  def encodeExamples(examples: Seq[Example]): Seq[ast.Exp] =
    examples.flatMap { example => encodeExample(example) }

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
    // method used to introduce auxiliary variables
    def auxiliary(expression: ast.Exp): (ast.LocalVar, ast.Exp) = {
      val name = s"t_${unique.getAndIncrement}"
      val variable = ast.LocalVar(name, ast.Bool)()
      val equality = ast.EqCmp(variable, expression)()
      (variable, equality)
    }

    // method used to introduce auxiliary variables.
    def auxiliaries(expressions: Iterable[ast.Exp]): (Seq[ast.LocalVar], Seq[ast.Exp]) =
      expressions
        .foldLeft((Seq.empty[ast.LocalVar], Seq.empty[ast.Exp])) {
          case ((variables, equalities), expression) =>
            val (variable, equality) = auxiliary(expression)
            (variables :+ variable, equalities :+ equality)
        }

    // method used to encode that at most one choice should be picked.
    def atMost(expressions: Seq[ast.Exp]): ast.Exp = {
      val constraints = Collections
        .pairs(expressions)
        .map { case (first, second) =>
          ast.Not(ast.And(first, second)())()
        }
      bigAnd(constraints)
    }

    // collect encodings and constraints
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
                val conjuncts = sequence.map { case (id, atoms) =>
                  val values = record.state.getValues(atoms)
                  encodeState(id, values, default)
                }
                Expressions.bigAnd(conjuncts)
              }
            }

          val (encodingVariables, equalities) = auxiliaries(encodings)
          val (variable, lower) = auxiliary(bigOr(encodingVariables))
          val upper = atMost(encodingVariables)
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

    val encoding =
      if (variables.isEmpty) ??? // was: true
      else ensureFraming(variables)._1

    (encoding, constraints)
  }

  /**
    * Computes the encoding of an abstract state defined by the given values for the guard with the given id.
    *
    * @param id      The id of the guard.
    * @param values  The values defining the state.
    * @param default The default value to assume for unknown atoms (approximation).
    * @return The encoding.
    */
  private def encodeState(id: Int, values: Seq[Option[Boolean]], default: Boolean): ast.Exp = {
    // encode clauses
    val clauses = for (j <- 0 until Settings.maxClauses) yield {
      val clauseActivation = ast.LocalVar(s"x_${id}_$j", ast.Bool)()
      val clauseEncoding = {
        // encode literals
        val literals = values
          .zipWithIndex
          .map { case (value, i) =>
            val literalActivation = ast.LocalVar(s"y_${id}_${i}_$j", ast.Bool)()
            val literalEncoding = value match {
              case Some(sign) =>
                val variable = ast.LocalVar(s"s_${id}_${i}_$j", ast.Bool)()
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
    * Collects the effective guards for the given template up to the given depth.
    *
    * @param template The template for which to collect the effective guards.
    * @param view     The view used to adapt expressions to the current context.
    * @param depth    The depth.
    * @return The collected effective guards.
    */
  private def collectGuards(template: Template, view: View, depth: Int): Map[ast.LocationAccess, Effective] = {
    val empty = Map.empty[ast.LocationAccess, Effective]
    if (depth == 0) empty
    else {
      // get and adapt atoms
      val atoms = template
        .atoms
        .map { atom => view.adapt(atom) }
      // process accesses
      template
        .body
        .foldLeft(empty) {
          case (result, resource) =>
            val guardId = resource.guardId
            resource.access match {
              case ast.FieldAccess(receiver, field) =>
                // update guard of field access
                val adapted = ast.FieldAccess(view.adapt(receiver), field)()
                val guard = result.getOrElse(adapted, Seq.empty) :+ Seq((guardId, atoms))
                result.updated(adapted, guard)
              case ast.PredicateAccess(arguments, name) =>
                // update guard of predicate access
                val adaptedArguments = arguments.map { argument => view.adapt(argument) }
                val adapted = ast.PredicateAccess(adaptedArguments, name)()
                val guard = result.getOrElse(adapted, Seq.empty) :+ Seq((guardId, atoms))
                val updated = result.updated(adapted, guard)
                // process nested accesses
                val innerTemplate = templates(name)
                val innerView = View.create(innerTemplate, adaptedArguments)
                collectGuards(innerTemplate, innerView, depth - 1).foldLeft(updated) {
                  case (innerResult, (innerAccess, innerGuard)) =>
                    val mappedGuard = innerGuard.map { choice => choice :+ (guardId, atoms) }
                    val updatedGuard = innerResult.getOrElse(innerAccess, Seq.empty) ++ mappedGuard
                    innerResult.updated(innerAccess, updatedGuard)
                }
            }
        }
    }
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
        case ast.LocalVar(name, _) => map(name)
      }
  }

}
