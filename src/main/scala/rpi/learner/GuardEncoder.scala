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

  private type Guard = Seq[Seq[(Int, Seq[sil.Exp])]]

  /**
    * Lazily compute all effective guards.
    */
  private lazy val guards =
    templates.map { case (name, template) =>
      // TODO: Depth depending on length of longest access path.
      name -> collectGuards(template, Store.empty, depth = 3)
    }

  val unique = new AtomicInteger

  /**
    * Computes the encoding for the given examples.
    *
    * @param examples The examples.
    * @return The encoding.
    */
  def encodeExamples(examples: Seq[Example]): sil.Exp = {
    if (Config.debugPrintGuards) {
      println("----- guards ------")
      guards.foreach { case (name, map) =>
        map.foreach { case (access, guard) =>
          val s = guard
            .map { choice =>
              choice
                .map { case (id, atoms) => s"phi_$id${atoms.mkString("[", ",", "]")}" }
                .mkString(" && ")
            }
            .mkString("{", ", ", "}")
          println(s"$access@$name: $s")
        }
      }
    }

    Expressions.bigAnd(examples.map(encodeExample))
  }

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
      // choices for this resource
      resourceGuards.map { sequence =>
        val conjuncts = sequence.map { case (id, atoms) =>
          val values = record.state.getValues(atoms)
          encodeState(id, values)
        }
        Expressions.bigAnd(conjuncts)
      }
    }

    // encode that only one choice can be picked
    val empty = Seq.empty[sil.Exp]
    val (auxiliaries, constraints) = choices.foldLeft((empty, empty)) {
      case ((variables, equalities), choice) =>
        val variable = sil.LocalVar(s"t_${unique.getAndIncrement()}", sil.Bool)()
        val equality = sil.EqCmp(variable, choice)()
        (variables :+ variable, equalities :+ equality)
    }

    // return full record encoding
    sil.And(Expressions.one(auxiliaries), Expressions.bigAnd(constraints))()
  }

  /**
    * Computes the encoding of the abstract state corresponding to the given values for the guard with the given id.
    *
    * @param id     The id of the guard.
    * @param values The values.
    * @return The encoding.
    */
  private def encodeState(id: Int, values: Seq[Boolean]): sil.Exp = {
    // encode clauses
    val clauses = for (j <- 0 until Config.maxClauses) yield {
      val clauseActivation = sil.LocalVar(s"x_${id}_$j", sil.Bool)()
      val clauseEncoding = {
        // encode literals
        val literals = values.zipWithIndex.map {
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

  private def collectGuards(template: Template, store: Store, depth: Int): Map[sil.LocationAccess, Guard] = {
    val empty = Map.empty[sil.LocationAccess, Guard]
    if (depth == 0) empty
    else {
      // get atoms
      val atoms = template.atoms.map { atom => store.adapt(atom) }
      // process accesses
      template
        .accesses
        .foldLeft(empty) {
          case (result, Guarded(id, access)) => access match {
            case sil.FieldAccess(receiver, field) =>
              // update guard of field access
              val adapted = sil.FieldAccess(store.adapt(receiver), field)()
              val updateGuard = result.getOrElse(adapted, Seq.empty) :+ Seq((id, atoms))
              result.updated(adapted, updateGuard)
            case sil.PredicateAccess(arguments, name) =>
              // update guard of predicate access
              val adaptedArguments = arguments.map { argument => store.adapt(argument) }
              val adapted = sil.PredicateAccess(adaptedArguments, name)()
              val updatedGuard = result.getOrElse(adapted, Seq.empty) :+ Seq((id, atoms))
              val updatedResult = result.updated(adapted, updatedGuard)
              // process nested location accesses
              val innerTemplate = templates(name)
              val parameters = innerTemplate.parameters
              val innerStore = Store(parameters.zip(adaptedArguments).toMap)
              collectGuards(innerTemplate, innerStore, depth - 1).foldLeft(updatedResult) {
                case (innerResult, (innerAccess, innerGuard)) =>
                  val mappedGuard = innerGuard.map { choice => choice :+ (id, atoms) }
                  val updatedGuard = innerResult.getOrElse(innerAccess, Seq.empty) ++ mappedGuard
                  innerResult.updated(innerAccess, updatedGuard)
              }
          }
        }
    }
  }
}

