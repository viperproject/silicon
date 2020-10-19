package rpi.learner

import java.util.concurrent.atomic.AtomicInteger

import rpi.util.Expressions
import rpi.{Example, Implication, Names, Negative, Positive, Record}
import viper.silver.{ast => sil}

/**
  * TODO: It might be better to encode to Z3 directly.
  *
  * @param templates The templates.
  */
class GuardEncoder(templates: Map[String, Template]) {
  private lazy val guards = {
    val empty = Map.empty[String, Map[Resource, Seq[Seq[(Int, View)]]]]
    templates.foldLeft(empty) {
      case (result, (name, template)) if name != Names.rec =>
        result.updated(name, collectGuards(template, View.empty, 2, templates))
      case (result, _) => result
    }
  }
  val id = new AtomicInteger

  /**
    * Computes the encoding for the given examples.
    *
    * @param examples The examples.
    * @return The encoding.
    */
  def encodeExamples(examples: Seq[Example]): sil.Exp =
    Expressions.bigAnd(examples.map(encodeExample))

  /**
    * Computes the encoding for the given example.
    *
    * @param example The example.
    * @return The encoding.
    */
  def encodeExample(example: Example): sil.Exp = example match {
    case Positive(record) => encodeRecord(record)
    case Negative(record) => sil.Not(encodeRecord(record))()
    case Implication(left, right) => sil.Implies(encodeRecord(left), encodeRecord(right))()
  }

  /**
    * Computes the encoding for the given record.
    *
    * @param record The record.
    * @return The encoding.
    */
  private def encodeRecord(record: Record): sil.Exp = {
    // get guards for program position
    val name = record.predicate.predicateName
    val localGuards = guards.getOrElse(name, Map.empty)
    // compute encoding for all choices
    val choices = record.paths.flatMap { path =>
      // get guards for resource
      val resource = Permission(path)
      val resourceGuards = localGuards.getOrElse(resource, Seq.empty)
      // choices for this resource
      resourceGuards.map { sequence =>
        val conjuncts = sequence.map { case (id, view) =>
          val state = if (view.isEmpty) record.abstraction else ???
          encodeState(id, state)
        }
        Expressions.bigAnd(conjuncts)
      }
    }
    // encode that only one choice can be picked
    // TODO: We might want to introduce temporary variables for the choices for better readability.

    val empty = Seq.empty[sil.Exp]
    val (auxiliaries, constraints) = choices.foldLeft((empty, empty)) {
      case ((variables, equalities), choice) =>
        val variable = sil.LocalVar(s"t_${id.getAndIncrement()}", sil.Bool)()
        val equality = sil.EqCmp(variable, choice)()
        (variables :+ variable, equalities :+ equality)
    }
    sil.And(Expressions.one(auxiliaries), Expressions.bigAnd(constraints))()
  }

  /**
    * Computes the encoding of a state abstracted by the given boolean vector for the guard with the given id.
    *
    * @param id    The id of the guard.
    * @param state The predicate abstraction of the state.
    * @return The encoding.
    */
  private def encodeState(id: Int, state: Seq[Boolean]): sil.Exp = {
    // complexity parameter
    // TODO: Make config.
    val k = 1
    // encode clauses
    val clauses = for (j <- 0 until k) yield {
      val clauseActivation = sil.LocalVar(s"x_${id}_$j", sil.Bool)()
      val clauseEncoding = {
        // encode literals
        val literals = state.zipWithIndex.map {
          case (value, i) =>
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

  private def collectGuards(template: Template, view: View, depth: Int, templates: Map[String, Template]): Map[Resource, Seq[Seq[(Int, View)]]] = {
    val empty = Map.empty[Resource, Seq[Seq[(Int, View)]]]
    if (depth == 0) empty
    else template
      .resources
      .foldLeft(empty) {
        case (result, Guarded(id, resource)) => resource match {
          case Permission(path) =>
            // update result with permission
            val adapted = Permission(view.adapt(path))
            result.updated(adapted, result.getOrElse(adapted, Seq.empty) :+ Seq((id, view)))
          case Predicate(name, arguments) =>
            // update result with predicate
            val adaptedArguments = arguments.map(view.adapt)
            val adapted = Predicate(name, adaptedArguments)
            val updatedResult = result.updated(adapted, result.getOrElse(adapted, Seq.empty) :+ Seq((id, view)))
            // process nested resources
            val innerTemplate = templates(name)
            val innerView = View(template.parameters.zip(adaptedArguments).toMap)
            collectGuards(innerTemplate, innerView, depth - 1, templates).foldLeft(updatedResult) {
              case (innerResult, (innerResource, innerGuards)) =>
                val mappedGuards = innerGuards.map { guards => guards :+ (id, view) }
                val updatedGuards = innerResult.getOrElse(innerResource, Seq.empty) ++ mappedGuards
                innerResult.updated(innerResource, updatedGuards)
            }
        }
      }
  }
}
