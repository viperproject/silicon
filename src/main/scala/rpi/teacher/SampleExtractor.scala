package rpi.teacher

import rpi.{Positive, Record, Sample}
import rpi.util.Maps
import viper.silicon.interfaces.SiliconNativeCounterexample
import viper.silicon.state.BasicChunk
import viper.silicon.state.terms.Term
import viper.silver.ast._
import viper.silver.verifier.VerificationError
import viper.silver.verifier.reasons.InsufficientPermission

object SampleExtractor {
  def extract(error: VerificationError, context: Context): Seq[Sample] = {
    val extractor = new SampleExtractor(error, context)
    extractor.extract()
  }
}

class SampleExtractor(error: VerificationError, context: Context) {
  /**
    * Type shortcuts.
    */
  type StoreMap = Map[String, Term]
  type HeapMap = Map[Term, StoreMap]
  type Path = Seq[String]
  type Paths = Set[Path]
  type Reachability = Map[Term, Paths]

  /**
    * The reason.
    */
  private lazy val reason = error.reason

  /**
    * The counter example.
    */
  private lazy val example = error.counterexample match {
    case Some(example: SiliconNativeCounterexample) => example
    case _ => ??? // wo do not expect anything other than native counter examples
  }

  /**
    * The store extracted from the counter example.
    */
  private lazy val store: StoreMap = example.store

  /**
    * The heap extracted from the counter example
    */
  private lazy val heap: HeapMap = example.heap
    .foldLeft(Map.empty: HeapMap)({
      case (partial, chunk: BasicChunk) =>
        // extract information from heap chunk
        val receiver = chunk.args.head
        val field = chunk.id.name
        val value = chunk.snap
        // update partial heap
        val fieldMap = partial.getOrElse(receiver, Map.empty)
        partial.updated(receiver, fieldMap.updated(field, value))
      case (partial, _) => partial
    })

  /**
    * Computes the terms that are reachable from the initial variables. The reachability is represented asa a map that
    * associates every reachable term with a set of access paths that point to that term.
    */
  private lazy val reachability: Reachability = {
    // auxiliary method that iteratively computes n-steps of the heap reachability
    def iterate(reachable: Reachability, n: Int): Reachability =
      if (n == 0) reachable
      else {
        // compute next step of the heap reachability
        val next = reachable.foldLeft(Map.empty: Reachability)({
          case (partial, (term, paths)) => heap
            .getOrElse(term, Map.empty)
            .foldLeft(partial)({
              case (partial, (field, value)) =>
                val existing = partial.getOrElse(value, Set.empty)
                partial.updated(value, existing ++ paths.map(_ :+ field))
            })
        })
        // recurse
        Maps.combine[Term, Paths](reachable, iterate(next, n - 1), _ ++ _)
      }

    // initialize reachability with terms directly pointed to by the initial variables
    val reachability = context.initials.keys
      .map(_.name)
      .foldLeft(Map.empty: Reachability)({
        case (partial, variable) =>
          val value = store(variable)
          val existing = partial.getOrElse(value, Set.empty)
          partial.updated(value, existing + Seq(variable))
      })

    // iteratively compute reachability
    iterate(reachability, 2)
  }

  private def evaluate(expression: Exp): Term = expression match {
    case LocalVar(name, _) => store(name)
    case FieldAccess(receiver, field) => heap(evaluate(receiver))(field.name)
    case _ => ???
  }

  //  TODO: Think of a better name.
  def initialExpression(term: Term): Set[Exp] = reachability(term)
    .map { path =>
      // TODO: Rework variables and fields
      val variable = context.initials(LocalVar(path.head, Ref)())
      path.tail.foldLeft(variable: Exp)({ case (receiver, field) => FieldAccess(receiver, Field(field, Ref)())() })
    }

  def extract(): Seq[Sample] = reason match {
    case InsufficientPermission(access) => access match {
      case FieldAccess(receiver, field) =>
        val term = evaluate(receiver)
        val expressions = initialExpression(term)
        assert(expressions.size == 1)
        val access = FieldAccess(expressions.head, field)()
        Seq(Positive(Record(access)))
    }
    case _ => Seq.empty
  }
}
