package rpi.teacher

import rpi._
import rpi.util.{Collections, UnionFind}
import viper.silicon.interfaces.SiliconRawCounterexample
import viper.silicon.state.{BasicChunk, Heap, Store, terms}
import viper.silicon.state.terms.Term
import viper.silver.ast.LocationAccess
import viper.silver.{ast => sil}
import viper.silver.verifier.{Model, SingleEntry, VerificationError}
import viper.silver.verifier.reasons.InsufficientPermission

/**
  * Extracts examples from verification errors.
  *
  * @param teacher The pointer to the teacher.
  */
class ExampleExtractor(teacher: Teacher) {
  /**
    * Returns the pointer to the inference.
    *
    * @return The inference.
    */
  def inference: Inference = teacher.inference

  /**
    * Extracts examples from the given verification error.
    *
    * @param error  The verification error.
    * @param triple The offending triple.
    * @return The extracted examples.
    */
  def extractExample(error: VerificationError, triple: Triple): Example = {
    // get counter-example
    val counter = error.counterexample match {
      case Some(value: SiliconRawCounterexample) => value
    }

    // extract states
    val (initial, current) = extractStates(counter)

    // extract location that caused the permission failure
    val offendingLocation = error.reason match {
      case InsufficientPermission(offending) => offending
    }

    // adapt the location to to its context if it comes from within a specification predicate
    val currentLocation =
      if (current.label == Labels.POST_STATE) {
        // get specification predicate and specification
        val predicate = getPredicate(triple.posts)
        val specification = inference.specifications(predicate.predicateName)
        // build formal-to-actual map
        val map = {
          val actuals = predicate.args
          val formals = specification.variables
          formals.zip(actuals).toMap
        }
        // adapt location
        offendingLocation.transform {
          case variable: sil.LocalVar => map(variable)
        }
      } else offendingLocation

    // the initial record
    lazy val initialRecord = {
      // get specification predicate and specification
      val predicate = getPredicate(triple.pres)
      val specification = inference.specifications(predicate.predicateName)
      // compute predicate abstraction of state
      val atoms = specification.atoms
      val abstraction = abstractState(initial, atoms)
      // map current location to initial specification predicate
      val initialLocations: Set[LocationAccess] = currentLocation match {
        case sil.FieldAccess(receiver, field) =>
          // compute paths that reach receiver
          val reachability = Reachability(initial)
          val term = current.evaluate(receiver)
          val paths = reachability.get(term)
          // build actual-to-formal map
          val map = {
            val actuals = predicate.args
            val formals = specification.variables
            actuals.zip(formals).toMap
          }
          // adapt receiver paths and create field accesses
          paths.map { path =>
            // TODO: Filter paths that cannot be adapted
            val adapted = path.transform {
              case variable: sil.LocalVar => map(variable)
            }
            sil.FieldAccess(adapted, field)()
          }
        case sil.PredicateAccess(arguments, name) =>
          // TODO: Implement me.
          ???
      }
      // create record
      Record(specification.predicate, abstraction, initialLocations)
    }

    // the current record
    lazy val currentRecord = {
      // get predicate and specifications
      val predicate = getPredicate(triple.posts)
      val specifications = inference.specifications(predicate.predicateName)
      // compute predicate abstraction of state
      val atoms = specifications.atoms
      val abstraction = abstractState(current, atoms)
      // create record
      Record(specifications.predicate, abstraction, Set(offendingLocation))
    }

    // create and return example
    if (current.label == Labels.POST_STATE) {
      // evaluate permission amount
      val variable = s"perm_${toSeq(currentLocation).mkString("_")}"
      val term = current.store(variable)
      val model = counter.model
      val permission = evaluate(term, model)
      // create implication or negative example depending on permission amount
      if (permission == "0.0") Implication(currentRecord, initialRecord)
      else Negative(currentRecord)
    } else Positive(initialRecord)
  }

  /**
    * TODO: Move to teacher and reuse in program builder.
    */
  private def toSeq(expression: sil.Exp): Seq[String] = expression match {
    case sil.LocalVar(name, _) => Seq(name)
    case sil.FieldAccess(receiver, field) => toSeq(receiver) :+ field.name
  }

  /**
    * Returns the predicate access corresponding to the inferred specifications.
    * TODO: Rework/remove this when reworking the triples.
    *
    * @param specifications The specifications.
    * @return The predicate.
    */
  private def getPredicate(specifications: Seq[sil.Exp]): sil.PredicateAccess =
    specifications
      .collectFirst {
        case sil.PredicateAccessPredicate(location, _) => location
      }
      .get

  /**
    * Returns the predicate abstraction of the given state.
    *
    * Note: The atomic predicates are only passed in order to know how many atomic predicates there are.
    *
    * @param state The state.
    * @param atoms The atomic predicates.
    * @return The predicate abstraction of the state.
    */
  private def abstractState(state: State, atoms: Seq[sil.Exp]): Seq[Boolean] =
    atoms
      .indices
      .map { i =>
        val variable = s"${state.label}_p_$i"
        state.store(variable) match {
          case terms.True() => true
          case terms.False() => false
        }
      }

  /**
    * Returns a pair of states where the first state is the pre-state and the second state is either the current state
    * or the post-state, depending on whether the execution failed or whether the assertion of the post-condition
    * failed.
    *
    * @param counter The counter-example.
    * @return The initial and the current state.
    */
  private def extractStates(counter: SiliconRawCounterexample): (State, State) = {
    // get path conditions and silicon state
    val conditions = counter.conditions
    val siliconState = counter.state

    // build partitions of equivalent terms
    val partitions = new UnionFind[Term]
    conditions.foreach {
      case terms.BuiltinEquals(left, right) =>
        partitions.union(left, right)
      case _ => // do nothing
    }

    // build store
    val siliconStore = siliconState.g
    val store = buildStore(siliconStore, partitions)

    // build heaps
    val siliconInitial = siliconState.oldHeaps(Labels.PRE_STATE)
    val siliconCurrent = siliconState.oldHeaps.getOrElse(Labels.POST_STATE, siliconState.h)
    val initialHeap = buildHeap(siliconInitial, partitions)
    val currentHeap = buildHeap(siliconCurrent, partitions)

    // build states
    // TODO: Possibly restrict stores?
    val currentLabel = {
      val isPost = siliconState.oldHeaps.isDefinedAt(Labels.POST_STATE)
      if (isPost) Labels.POST_STATE else Labels.CURRENT_STATE
    }
    val initial = State(Labels.PRE_STATE, store, initialHeap)
    val current = State(currentLabel, store, currentHeap)

    // return states
    (initial, current)
  }

  /**
    * Builds a store map from a Silicon store.
    *
    * @param store      The store.
    * @param partitions The partitions of equivalent terms.
    * @return The store map.
    */
  private def buildStore(store: Store, partitions: UnionFind[Term]): Map[String, Term] =
    store
      .values
      .map { case (variable, term) =>
        val value = partitions.find(term)
        variable.name -> value
      }

  /**
    * Builds a heap map from a Silicon heap.
    *
    * @param heap       The heap.
    * @param partitions The partitions of equivalent terms.
    * @return The heap map.
    */
  private def buildHeap(heap: Heap, partitions: UnionFind[Term]): Map[Term, Map[String, Term]] = {
    val empty = Map.empty[Term, Map[String, Term]]
    heap
      .values
      .foldLeft(empty) {
        case (result, chunk: BasicChunk) =>
          // extract information from heap chunk
          val receiver = partitions.find(chunk.args.head)
          val field = chunk.id.name
          val value = partitions.find(chunk.snap)
          // update heap map
          val fields = result
            .getOrElse(receiver, Map.empty)
            .updated(field, value)
          result.updated(receiver, fields)
      }
  }

  /**
    * A state extracted from the Silicon verifier.
    *
    * @param label The label allowing to identify a specific state.
    * @param store The store.
    * @param heap  The heap.
    */
  private case class State(label: String, store: Map[String, Term], heap: Map[Term, Map[String, Term]]) {
    /**
      * Evaluates the given Silver expression into a Silicon term.
      *
      * @param expression The expression to evaluate.
      * @return The resulting term.
      */
    def evaluate(expression: sil.Exp): Term = expression match {
      case sil.LocalVar(name, _) => store(name)
      case sil.FieldAccess(receiver, field) => heap(evaluate(receiver))(field.name)
    }
  }

  /**
    * A helper class used to express the reachability of terms in a state.
    *
    * @param state The state.
    */
  private case class Reachability(state: State) {
    /**
      * The reachability map.
      */
    private lazy val map = recurse(initial, steps = 3)

    /**
      * Returns the reachability of the given term.
      *
      * @param term The term.
      * @return The paths.
      */
    def get(term: Term): Set[sil.Exp] = map(term)

    /**
      * Returns the reachability map of everything that is directly reachable from the store of the state.
      *
      * @return The initial reachability map.
      */
    private def initial: Map[Term, Set[sil.Exp]] = {
      val empty = Map.empty[Term, Set[sil.Exp]]
      state
        .store
        .filterKeys(_.endsWith("_init"))
        .foldLeft(empty) {
          case (result, (initial, term)) =>
            val variable = sil.LocalVar(initial.dropRight(5), sil.Ref)()
            val variables = result.getOrElse(term, Set.empty) + variable
            result.updated(term, variables)
        }
    }

    /**
      * Updates the current reachability map by recursing the given number of steps.
      *
      * @param current The current reachability map.
      * @param steps   The number of steps.
      * @return The reachability map.
      */
    private def recurse(current: Map[Term, Set[sil.Exp]], steps: Int): Map[Term, Set[sil.Exp]] =
      if (steps == 0) current
      else {
        // compute next step of the reachability map
        val empty = Map.empty[Term, Set[sil.Exp]]
        val next = current.foldLeft(empty) {
          case (map1, (term, paths)) =>
            state.heap.getOrElse(term, Map.empty).foldLeft(map1) {
              case (map2, (name, value)) =>
                val field = sil.Field(name, sil.Ref)()
                val extendedPaths = paths.map { path => sil.FieldAccess(path, field)() }
                val updatedPaths = map2.getOrElse(value, Set.empty) ++ extendedPaths
                map2.updated(value, updatedPaths)
            }
        }
        // recurse and combine results
        Collections.combine[Term, Set[sil.Exp]](current, recurse(next, steps - 1), _ ++ _)
      }
  }

  /**
    * Evaluates the given term in the given model.
    *
    * @param term  The term to evaluate.
    * @param model The model.
    * @return The value of the term in the given model.
    */
  private def evaluate(term: Term, model: Model): String = term match {
    // variable
    case terms.Var(id, _) => model.entries.get(id.name) match {
      case Some(SingleEntry(value)) => value
      case _ => ???
    }
    // ???
    case terms.SortWrapper(wrapped, _) => evaluate(wrapped, model)
    case terms.First(arg) => s"fst(${evaluate(arg, model)})"
    case terms.Second(arg) => s"snd(${evaluate(arg, model)}"
    // permissions
    case terms.FullPerm() => "1.0"
    case terms.NoPerm() => "0.0"
    case terms.PermPlus(left, right) =>
      val leftValue = evaluate(left, model).toDouble
      val rightValue = evaluate(right, model).toDouble
      String.valueOf(leftValue + rightValue)
    // boolean terms
    case terms.BuiltinEquals(left, right) =>
      val leftValue = evaluate(left, model)
      val rightValue = evaluate(right, model)
      String.valueOf(leftValue == rightValue)
    case terms.Ite(cond, left, right) =>
      evaluate(cond, model) match {
        case "true" => evaluate(left, model)
        case "false" => evaluate(right, model)
      }
    case _ => ???
  }

}
