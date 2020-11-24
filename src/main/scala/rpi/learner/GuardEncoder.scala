package rpi.learner

import java.util.concurrent.atomic.AtomicInteger

import rpi.Config
import rpi.inference._
import rpi.util.Expressions
import viper.silver.{ast => sil}

class GuardEncoder(learner: Learner, templates: Map[String, Template]) {
  /**
    * Type shortcut for an effective guard.
    *
    * The outer sequence represents a choice of exactly one of the options. The inner sequence represents a disjunction
    * of guards. The guards are represented by their id and which atomic predicates of the context correspond to the
    * atomic predicates of the guard.
    */
  private type Guard = Seq[Seq[(Int, Seq[sil.Exp])]]

  private val guards: Map[String, Map[sil.LocationAccess, Guard]] =
    templates.map { case (name, template) =>
      // TODO: Depth depending on length of longest access path.
      name -> collectGuards(template, View.empty, depth = 3)
    }

  private val unique = new AtomicInteger

  def encodeExamples(examples: Seq[Example]): sil.Exp = {
    // encode examples
    val encoded = examples.map { example => encodeExample(example) }
    Expressions.bigAnd(encoded)
  }

  def encodeExample(example: Example): sil.Exp =
    example match {
      case Positive(record) => encodeRecord(record)
      case Negative(record) => sil.Not(encodeRecord(record))()
      case Implication(left, right) => sil.Implies(encodeRecord(left), encodeRecord(right))()
    }

  def encodeRecord(record: Record): sil.Exp = {
    val name = record.specification.name
    val localGuards = guards.getOrElse(name, Map.empty)

    // compute encoding for all choices
    val choices = record
      .locations
      .flatMap { location =>
        // get guard for location
        val locationGuard = localGuards.getOrElse(location, Seq.empty)
        // choices for this location
        locationGuard.map { sequence =>
          val conjuncts = sequence.map { case (id, atoms) =>
            val values = record.state.getValues(atoms)
            encodeState(id, values)
          }
          Expressions.bigAnd(conjuncts)
        }
      }

    // encode that only one choice can be picked
    val (auxiliaries, constraints) = {
      val empty = Seq.empty[sil.Exp]
      choices.foldLeft((empty, empty)) {
        case ((variables, equalities), choice) =>
          val variable = sil.LocalVar(s"t_${unique.getAndIncrement()}", sil.Bool)()
          val equality = sil.EqCmp(variable, choice)()
          (variables :+ variable, equalities :+ equality)
      }
    }

    // return encoding
    sil.And(Expressions.one(auxiliaries), Expressions.bigAnd(constraints))()
  }

  /**
    * Computes the encoding of an abstract state defined by the given values for the guard with the given id.
    *
    * TODO: Approximation.
    *
    * @param id     The id of the guard.
    * @param values The values defining the state.
    * @return The encoding.
    */
  private def encodeState(id: Int, values: Seq[Boolean]): sil.Exp = {
    // encode clauses
    val clauses = for (j <- 0 until Config.maxClauses) yield {
      val clauseActivation = sil.LocalVar(s"x_${id}_$j", sil.Bool)()
      val clauseEncoding = {
        // encode literals
        val literals = values
          .zipWithIndex
          .map { case (value, i) =>
            val literalActivation = sil.LocalVar(s"y_${id}_${i}_$j", sil.Bool)()
            val literalEncoding = {
              val sign = sil.LocalVar(s"s_${id}_${i}_$j", sil.Bool)()
              if (value) sign else sil.Not(sign)()
            }
            sil.Implies(literalActivation, literalEncoding)()
          }
        // conjoin all literals
        Expressions.bigAnd(literals)
      }
      sil.And(clauseActivation, clauseEncoding)()
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
  private def collectGuards(template: Template, view: View, depth: Int): Map[sil.LocationAccess, Guard] = {
    val empty = Map.empty[sil.LocationAccess, Guard]
    if (depth == 0) empty
    else {
      // get and adapt atoms
      val atoms = template
        .atoms
        .map { atom => view.adapt(atom) }
      // process accesses
      template
        .accesses
        .foldLeft(empty) {
          case (result, Guarded(id, access)) => access match {
            case sil.FieldAccess(receiver, field) =>
              // update guard of field access
              val adapted = sil.FieldAccess(view.adapt(receiver), field)()
              val guard = result.getOrElse(adapted, Seq.empty) :+ Seq((id, atoms))
              result.updated(adapted, guard)
            case sil.PredicateAccess(arguments, name) =>
              // update guard of predicate access
              val adaptedArguments = arguments.map { argument => view.adapt(argument) }
              val adapted = sil.PredicateAccess(adaptedArguments, name)()
              val guard = result.getOrElse(adapted, Seq.empty) :+ Seq((id, atoms))
              val updated = result.updated(adapted, guard)
              // process nested accesses
              val innerTemplate = templates(name)
              val innerView = View.create(innerTemplate, adaptedArguments)
              collectGuards(innerTemplate, innerView, depth - 1).foldLeft(updated) {
                case (innerResult, (innerAccess, innerGuard)) =>
                  val mappedGuard = innerGuard.map { choice => choice :+ (id, atoms) }
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

    def create(template: Template, arguments: Seq[sil.Exp]): View = {
      val names = template
        .specification
        .parameters
        .map { parameter => parameter.name }
      View(names.zip(arguments).toMap)
    }
  }

  case class View(map: Map[String, sil.Exp]) {
    def isEmpty: Boolean = map.isEmpty

    def adapt(expression: sil.Exp): sil.Exp =
      if (isEmpty) expression
      else expression.transform {
        case sil.LocalVar(name, _) => map(name)
      }
  }

}
