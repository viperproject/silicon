package rpi.teacher

import rpi._
import rpi.util.{Collections, UnionFind}
import viper.silicon.interfaces.SiliconRawCounterexample
import viper.silicon.state.{BasicChunk, Heap, Store, terms}
import viper.silicon.state.terms.Term
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
    * @return The pointer to the inference.
    */
  def inference: Inference = teacher.inference

  /**
    * Extracts an example from the given verification error.
    *
    * @param error        The verification error.
    * @param preInstance  The instance of the precondition to infer.
    * @param postInstance The instance of the postcondition to infer.
    */
  def extract(error: VerificationError, preInstance: Instance, postInstance: Instance): Example = {
    // debug output
    if (Config.debugPrintError) {
      println("----- error -----")
      println(error)
    }

    // extract states and model
    val counter = error.counterexample match {
      case Some(value: SiliconRawCounterexample) => value
    }
    val (preState, currentState) = extractStates(counter)
    val model = counter.model

    // extract offending location that caused permission failure
    val offendingLocation = error.reason match {
      case InsufficientPermission(location) => location
    }
    // adapt offending location to current state
    val isPost = currentState.label == Labels.POST_STATE
    val currentLocations =
      if (isPost) offendingLocation match {
        case sil.FieldAccess(receiver, field) =>
          sil.FieldAccess(postInstance.toActual(receiver), field)()
        case sil.PredicateAccess(arguments, name) =>
          val updated = arguments.map { argument => postInstance.toActual(argument) }
          sil.PredicateAccess(updated, name)()
      }
      else offendingLocation


    // pre record
    val preRecord = {
      val adaptor = Adaptor(preState, currentState, preInstance)
      val predicate = preInstance.specification.predicate
      val state =
        if (isPost) {
          // combine information from pre and post state
          val preAbstraction = abstractState(preState, preInstance.formalAtoms)
          val postAbstraction = abstractState(currentState, postInstance.actualAtoms)
          preAbstraction.meet(adaptor.adaptState(postAbstraction))
        } else abstractState(preState, preInstance.formalAtoms)
      val locations = adaptor.adaptLocation(currentLocations)
      Record(predicate, state, locations)
    }

    // post record
    lazy val postRecord = {
      val predicate = postInstance.specification.predicate
      val locations = Set(offendingLocation)
      val state = abstractState(currentState, postInstance.formalAtoms)
      Record(predicate, state, locations)
    }

    // create example
    if (isPost) {
      // evaluate permission amount
      val variable = s"perm_${teacher.encode(currentLocations)}"
      val term = currentState.store(variable)
      val permission = evaluate(term, model)
      // create implication or negative example depending on permission amount
      if (permission == "0.0") Implication(postRecord, preRecord)
      else Negative(postRecord)
    } else Positive(preRecord)
  }

  /**
    * Extracts the pre state and the current state from the counter-example. The current state represents the state at
    * which the error happened.
    *
    * @param counter The counterexample.
    * @return The pre-state and the current state.
    */
  private def extractStates(counter: SiliconRawCounterexample): (State, State) = {
    // get path conditions and silicon state
    val conditions = counter.conditions
    val state = counter.state

    // build partitions of equivalent terms
    val partitions = new UnionFind[Term]
    conditions.foreach {
      case terms.BuiltinEquals(left, right) =>
        partitions.union(left, right)
      case _ => // do nothing
    }

    // build store
    val siliconStore = state.g
    val store = buildStore(siliconStore, partitions)

    // build heaps
    val initialPre = state.oldHeaps(Labels.PRE_STATE)
    val siliconCurrent = state.oldHeaps.getOrElse(Labels.POST_STATE, state.h)
    val preHeap = buildHeap(initialPre, partitions)
    val currentHeap = buildHeap(siliconCurrent, partitions)

    // build states
    // TODO: Possibly restrict stores?
    val currentLabel = {
      val isPost = state.oldHeaps.isDefinedAt(Labels.POST_STATE)
      if (isPost) Labels.POST_STATE else Labels.CURRENT_STATE
    }
    val preState = State(Labels.PRE_STATE, store, preHeap)
    val currentState = State(currentLabel, store, currentHeap)

    // return states
    (preState, currentState)
  }

  /**
    * Builds a store map from a silicon store.
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
    * Builds a heap map from a silicon heap.
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
    * Returns an abstraction of the given state.
    *
    * NOTE: The atomic predicates have to be in their canonical order.
    *
    * @param state The state.
    * @param atoms The atomic predicates.
    * @return The abstracted state.
    */
  private def abstractState(state: State, atoms: Seq[sil.Exp]): AbstractState = {
    val pairs = atoms
      .zipWithIndex
      .map { case (atom, i) =>
        val variable = s"${state.label}_p_$i"
        state.store(variable) match {
          case terms.True() => (atom, true)
          case terms.False() => (atom, false)
        }
      }
    AbstractState(pairs)
  }

  /**
    * A state extracted from the silicon verifier.
    *
    * @param label The label identifying the state.
    * @param store The store.
    * @param heap  The heap.
    */
  private case class State(label: String, store: Map[String, Term], heap: Map[Term, Map[String, Term]]) {
    /**
      * Evaluates the given silver expression into a silicon term.
      *
      * @param expression The expression to evaluate
      * @return The resulting term
      */
    def evaluate(expression: sil.Exp): Term = expression match {
      case sil.LocalVar(name, _) => store(name)
      case sil.FieldAccess(receiver, field) => heap(evaluate(receiver))(field.name)
    }
  }

  private case class Adaptor(preState: State, currentState: State, preInstance: Instance) {
    /**
      * The reachability map.
      *
      * TODO: Number of steps.
      */
    private val reachability = recurse(initial, steps = 3)

    /**
      * Adapts the given expression.
      *
      * @param expression The expression to adapt.
      * @return A set of expressions that can be used to express the given expression in the pre-state.
      */
    def adaptPath(expression: sil.Exp): Set[sil.Exp] = {
      val term = preState.evaluate(expression)
      reachability
        .getOrElse(term, Set.empty)
        .map { adapted => preInstance.toFormal(adapted) }
    }

    def adapt(expression: sil.Exp): Set[sil.Exp] =
      expression match {
        case _: sil.LocalVar | _: sil.FieldAccess => adaptPath(expression)
        case _: sil.NullLit => Set(expression)
        case sil.EqCmp(left, right) => for (l <- adapt(left); r <- adapt(right)) yield sil.EqCmp(l, r)()
        case sil.NeCmp(left, right) => for (l <- adapt(left); r <- adapt(right)) yield sil.NeCmp(l, r)()
        case _ => ???
      }

    def adaptLocation(location: sil.LocationAccess): Set[sil.LocationAccess] = location match {
      case sil.FieldAccess(receiver, field) =>
        adapt(receiver).map { adapted => sil.FieldAccess(adapted, field)() }
      case sil.PredicateAccess(arguments, name) =>
        val combinations = Collections.product(arguments.map(adapt))
        combinations.map { combination => sil.PredicateAccess(combination, name)() }
    }

    def adaptState(state: AbstractState): AbstractState = {
      val pairs = state.pairs.flatMap { case (atom, value) =>
        adapt(atom).map { adapted => (adapted, value) }
      }
      AbstractState(pairs)
    }

    /**
      * Returns the reachability map of everything that is directly reachable from the store of the state.
      *
      * @return The initial reachability map.
      */
    private def initial: Map[Term, Set[sil.Exp]] = {
      val empty = Map.empty[Term, Set[sil.Exp]]
      currentState
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
      * @param map   The current reachability map.
      * @param steps The number of steps.
      * @return The reachability map.
      */
    private def recurse(map: Map[Term, Set[sil.Exp]], steps: Int): Map[Term, Set[sil.Exp]] =
      if (steps == 0) map
      else {
        // compute next step of the reachability map
        val empty = Map.empty[Term, Set[sil.Exp]]
        val next = map.foldLeft(empty) {
          case (map1, (term, paths)) =>
            currentState.heap.getOrElse(term, Map.empty).foldLeft(map1) {
              case (map2, (name, value)) =>
                val field = sil.Field(name, sil.Ref)()
                val extendedPaths = paths.map { path => sil.FieldAccess(path, field)() }
                val updatedPaths = map2.getOrElse(value, Set.empty) ++ extendedPaths
                map2.updated(value, updatedPaths)
            }
        }
        // recurse and combine results
        Collections.combine[Term, Set[sil.Exp]](map, recurse(next, steps - 1), _ ++ _)
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
