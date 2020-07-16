package rpi.learner

import rpi._
import viper.silver.ast._

class Learner {
  /**
    * The samples.
    */
  private var samples: Seq[Sample] = Seq.empty

  private def positives(): Seq[Positive] = samples.collect({ case positive: Positive => positive })

  private def negatives(): Seq[Negative] = samples.collect({ case negative: Negative => negative })

  private def implications(): Seq[Implication] = samples.collect({ case implication: Implication => implication })

  def addSamples(samples: Seq[Sample]): Unit = this.samples ++= samples

  def hypothesis(): Exp = positives()
    .map(_.record.access)
    .map(FieldAccessPredicate(_, FullPerm()())())
    .reduce[Exp](And(_, _)())

  /**
    * TODO: Implement properly. This is just a test.
    */
  def extractPredicate(): Unit = {
    def commonSuffix(left: Exp, right: Exp): (Exp, Exp, Seq[Field]) = (left, right) match {
      case (FieldAccess(leftReceiver, field), FieldAccess(rightReceiver, rightField)) if field == rightField =>
        val (leftPrefix, rightPrefix, suffix) = commonSuffix(leftReceiver, rightReceiver)
        (leftPrefix, rightPrefix, suffix :+ field)
      case _ => (left, right, Seq.empty)
    }

    def getVariable(expression: Exp): LocalVar = expression match {
      case variable: LocalVar => variable
      case FieldAccess(receiver, _) => getVariable(receiver)
    }

    def pairs[A](sequence: Seq[A]): Seq[(A, A)] =
      if (sequence.isEmpty) Seq.empty
      else sequence.tail.map((sequence.head, _)) ++ pairs(sequence.tail)

    val accesses = samples.flatMap {
      case Positive(Record(_, access)) => Seq(access)
      case Negative(Record(_, access)) => Seq(access)
      case Implication(Record(_, left), Record(_, right)) => Seq(left, right)
    }

    val map = accesses
      .foldLeft(Map.empty[Field, Set[Exp]])({
        case (map, FieldAccess(receiver, field)) =>
          val existing = map.getOrElse(field, Set.empty)
          map.updated(field, existing + receiver)
      })

    val recursions = map
      .flatMap({ case (field, set) => pairs(set.toSeq)
        .flatMap({
          case (left, right) =>
            commonSuffix(left, right) match {
              case (variable: LocalVar, expression, _) if getVariable(expression) == variable => Some(variable, expression)
              case (expression, variable: LocalVar, _) if getVariable(expression) == variable => Some(variable, expression)
              case _ => None
            }
        })
      })

    val fields = accesses.collect({
      case FieldAccess(_, field) => field
    }).toSet

    val parameters = recursions.keys.map(variable => LocalVarDecl(variable.name, variable.typ)()).toSeq

    val r1 = recursions
      .flatMap({ case (from, to) => fields.
        flatMap({ field =>
          val fromAccess = FieldAccess(from, field)()
          val toAccess = FieldAccess(to, field)()
          if (accesses.contains(fromAccess) && accesses.contains(toAccess)) Some(FieldAccessPredicate(fromAccess, FullPerm()())())
          else None

        })
      })
    val r2 = recursions.map({ case (_, to) => PredicateAccess(Seq(to), "P")() })
    val body = (r1 ++ r2).reduceOption[Exp](And(_, _)())
    val predicate = Predicate("P", parameters, body)()

    println(predicate)

    // TODO: Handle multiple parameters

  }
}
