package rpi.learner

import java.util.concurrent.atomic.AtomicInteger

import rpi.util.Expressions
import rpi._
import viper.silver.{ast => sil}

/**
  * TODO: It might be better to encode to Z3 directly.
  *
  * @param templates The templates.
  */
class GuardEncoder(learner: Learner, templates: Map[String, Template]) {

  def inference: Inference = learner.inference

  /**
    * Lazily compute all effective guards.
    */
  private lazy val guards =
    templates.flatMap {
      case (name, template) =>
        inference.specifications.get(name).map {
          specification =>
            val atoms = specification.atoms
            name -> collectGuards(template, Store.empty, atoms, depth = 2)
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
    val choices = record.locations.flatMap { resource =>
      // get guards for resource
      val resourceGuards = localGuards.getOrElse(resource, Seq.empty)
      println(s"$resource: $resourceGuards")
      // choices for this resource
      resourceGuards.map { sequence =>
        val conjuncts = sequence.map { case (guardId, view) =>
          // TODO: Handle cases where there is view of an atomic predicate
          val x = view.adapt(record.abstraction)
          val state = x.map(_.get)
          encodeState(guardId, state)
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
    // encode clauses
    val clauses = for (j <- 0 until Config.maxClauses) yield {
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

  private def collectGuards(template: Template, store: Store, atoms: Seq[sil.Exp], depth: Int): Map[sil.LocationAccess, Seq[Seq[(Int, View)]]] = {
    // compute view
    val view =
      if (store.isEmpty) View.identity
      else {
        val localAtoms = template.specification.atoms
        val adapted = localAtoms.map { atom => store.adapt(atom) }
        View.mapped(atoms, adapted)
      }

    val empty = Map.empty[sil.LocationAccess, Seq[Seq[(Int, View)]]]
    if (depth == 0) empty
    else template
      .resources
      .foldLeft(empty) {
        case (result, Guarded(guardId, access)) => access match {
          case sil.FieldAccess(receiver, field) =>
            // update result with permission for field access
            val adapted = sil.FieldAccess(store.adapt(receiver), field)()
            val updatedGuards = result.getOrElse(adapted, Seq.empty) :+ Seq((guardId, view))
            result.updated(adapted, updatedGuards)
          case sil.PredicateAccess(arguments, name) =>
            // update result with permission for predicate access
            val adaptedArguments = arguments.map { argument => store.adapt(argument) }
            val adapted = sil.PredicateAccess(adaptedArguments, name)()
            val updatedGuards = result.getOrElse(adapted, Seq.empty) :+ Seq((guardId, view))
            val updatedResult = result.updated(adapted, updatedGuards)
            // process nested location accesses
            val innerTemplate = templates(name)
            val parameters = innerTemplate.parameters
            val innerStore = Store(parameters.zip(adaptedArguments).toMap)
            collectGuards(innerTemplate, innerStore, atoms, depth - 1).foldLeft(updatedResult) {
              case (innerResult, (innerAccess, innerGuards)) =>
                val mappedGuards = innerGuards.map { guards => guards :+ (guardId, view) }
                val updatedGuards = innerResult.getOrElse(innerAccess, Seq.empty) ++ mappedGuards
                innerResult.updated(innerAccess, updatedGuards)
            }
        }
      }
  }
}

