package rpi.teacher

import rpi.{Positive, Record, Sample}
import rpi.util.{Maps, UnionFind}
import viper.silicon.interfaces.SiliconRawCounterexample
import viper.silicon.interfaces.state.Chunk
import viper.silicon.state.BasicChunk
import viper.silicon.state.terms.{BuiltinEquals, Term}
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
    * The verifier state from the silicon counter example
    */
  private lazy val (conditions, state) = error.counterexample match {
    case Some(SiliconRawCounterexample(cs, s, _)) => (cs, s)
    case _ => ??? // wo do not expect anything other than raw counter examples
  }

  private val x = {
    val uf = new UnionFind[Term]

    conditions.foreach {
      case BuiltinEquals(a, b) =>
        uf.add(a)
        uf.add(b)
        uf.union(a, b)
      case _ => // do nothing
    }

    println(conditions)
    println(uf.toString)

    uf
  }

  /**
    * The initial state.
    */
  private lazy val initialState = {
    val store = buildStoreMap(context.args())
    val heap = buildHeapMap(state.oldHeaps(Teacher.PRE_STATE_LABEL).values)
    State(store, heap)
  }

  /**
    * The current state.
    */
  private lazy val currentState = {
    val store = buildStoreMap(context.vars())
    // TODO: fix
    val heap = buildHeapMap(state.oldHeaps.getOrElse(Teacher.POST_STATE_LABEL, state.h).values)
    State(store, heap)
  }

  /**
    * Computes the terms that are reachable from the initial variables. The reachability is represented as a map that
    * associates every reachable term with a set of access paths that point to that term (in the initial state).
    */
  private lazy val reachability: Reachability = {
    // auxiliary method that iteratively computes n steps of the heap reachability
    def iterate(reachable: Reachability, n: Int): Reachability =
      if (n == 0) reachable
      else {
        // compute next step of the heap reachability
        val next = reachable
          .foldLeft(Map.empty: Reachability)({
            case (partial, (term, paths)) => initialState.heap
              .getOrElse(term, Map.empty).foldLeft(partial) {
              case (partial, (field, value)) =>
                val existing = partial.getOrElse(value, Set.empty)
                partial.updated(value, existing ++ paths.map(_ :+ field))
            }
          })
        // recurse and combine results
        Maps.combine[Term, Paths](reachable, iterate(next, n - 1), _ ++ _)
      }

    // compute store reachability
    val reachability = initialState.store
      .foldLeft(Map.empty: Reachability)({
        case (partial, (variable, value)) =>
          val existing = partial.getOrElse(value, Set.empty)
          partial.updated(value, existing + Seq(variable))
      })

    // iteratively compute heap reachability
    iterate(reachability, 2)
  }

  private def buildStoreMap(vars: Seq[LocalVarDecl]): StoreMap = vars.map(v => v.name -> x.find(state.g(LocalVar(v.name, v.typ)()))).toMap

  private def buildHeapMap(chunks: Iterable[Chunk]): HeapMap = chunks.foldLeft[HeapMap](Map.empty) {
    case (partial, chunk: BasicChunk) =>
      // extract information from heap chunk
      val receiver = x.find(chunk.args.head)
      val field = chunk.id.name
      val value = x.find(chunk.snap)
      // update partial heap
      val fieldMap = partial.getOrElse(receiver, Map.empty)
      partial.updated(receiver, fieldMap.updated(field, value))
    case (partial, _) => ???
  }

  private def adapt(expression: Exp): Set[Exp] = {
    val term = currentState.evaluate(expression)
    val initials = (context.args().map(_.name) zip context.vars()).toMap
    reachability(term).map { path =>
      val declaration = initials(path.head)
      val variable = LocalVar(declaration.name, declaration.typ)()
      path.tail.foldLeft(variable: Exp)({
        case (receiver, field) => FieldAccess(receiver, Field(field, Ref)())()
      })
    }
  }

  def extract(): Seq[Sample] = reason match {
    case InsufficientPermission(FieldAccess(receiver, field)) =>
      println(initialState)
      println(currentState)
      val adapted = adapt(receiver)
      assert(adapted.size == 1)
      val access = FieldAccess(adapted.head, field)()
      Seq(Positive(Record(access)))
  }


  case class State(store: StoreMap, heap: HeapMap) {
    /**
      * Evaluates the given expression in this state.
      *
      * @param expression The expression to evaluate.
      * @return The value of the expression.
      */
    def evaluate(expression: Exp): Term = expression match {
      case LocalVar(variable, _) => store(variable)
      case FieldAccess(receiver, Field(field, _)) => heap(evaluate(receiver))(field)
      case _ => ???
    }
  }

}
