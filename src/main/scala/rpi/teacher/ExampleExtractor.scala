package rpi.teacher

import rpi.inference._
import rpi.util.{Collections, UnionFind}
import viper.silicon.interfaces.SiliconRawCounterexample
import viper.silicon.state._
import viper.silicon.state.terms.Term
import viper.silver.ast.SimpleInfo
import viper.silver.verifier.{Model, SingleEntry, VerificationError}
import viper.silver.verifier.reasons.InsufficientPermission
import viper.silver.{ast => sil}

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
    * @param error The verification error.
    * @return The extracted example.
    */
  def extract(error: VerificationError, context: Context): Example = {
    // extract counter example and offending location
    val counter = extractCounter(error)
    // TODO: I don't like how the optional label is handeled further down.
    val (offending, label) = extractOffending(error)


    // extract states
    val (currentState, otherStates) = extractStates(counter, label)

    val currentLocation = label match {
      case Some(name) => context
        .instance(name)
        .toActual(offending)
      case _ => offending
    }

    lazy val preRecord = {
      // TODO: Allow multiple?!
      assert(otherStates.length == 1)
      otherStates
        .map { otherState =>
          val otherInstance = context.instance(otherState.name)
          val adaptor = Adaptor(currentState, otherState, otherInstance)
          val state =
            if (label.isDefined) {
              // combine information from pre and post state
              val currentInstance = context.instance(label.get)
              val pre = abstractState(otherState, otherInstance)
              val post = abstractState(currentState, currentInstance)
              pre.meet(adaptor.adaptState(post))
            } else abstractState(otherState, otherInstance)
          // TODO: It could be beneficial to have a set of all equivalent locations.
          val locations = adaptor.adaptLocation(currentLocation)
          Record(otherInstance.specification, state, locations)
        }
        .head
    }

    // post record
    lazy val postRecord = {
      val currentInstance = context.instance(label.get)
      val state = abstractState(currentState, currentInstance)
      val locations = Set(offending)
      Record(currentInstance.specification, state, locations)
    }

    // create example
    if (label.isDefined) {
      // evaluate permission amount
      val variable = context.variable(currentLocation)
      val term = currentState.store(variable)
      val permission = currentState.evaluatePermission(term)
      // create implication or negative example depending on permission amount
      if (permission == 0) Implication(postRecord, preRecord)
      else Negative(postRecord)
    } else Positive(preRecord)
  }

  /**
    * Extracts the counter example from the verification error.
    *
    * @param error The verification error.
    * @return The counter example.
    */
  private def extractCounter(error: VerificationError): SiliconRawCounterexample =
    error.counterexample match {
      case Some(value: SiliconRawCounterexample) => value
    }

  private def extractOffending(error: VerificationError): (sil.LocationAccess, Option[String]) = {
    val location = error.reason match {
      case InsufficientPermission(access) => access
    }
    val label = error.offendingNode match {
      case fold: sil.Fold => fold
        .info
        .getUniqueInfo[SimpleInfo]
        .flatMap { info => info.comment.headOption }
      case _ => None
    }

    (location, label)
  }

  private def extractStates(counter: SiliconRawCounterexample, label: Option[String]): (State, Seq[State]) = {
    // build partitions of equivalent terms
    // TODO: This might be replaced by evaluating the model?
    val partitions = new UnionFind[Term]
    counter.conditions.foreach {
      case terms.BuiltinEquals(left, right) =>
        partitions.union(left, right)
      case _ => // do nothing
    }

    val state = counter.state
    val model = counter.model

    // build store
    // TODO: Restrict stores?
    val siliconStore = state.g
    val store = buildStore(siliconStore, partitions)

    // current state
    val current = {
      val siliconHeap = label
        .flatMap { name => state.oldHeaps.get(name) }
        .getOrElse(state.h)
      val name = label.getOrElse("current")
      val heap = buildHeap(siliconHeap, partitions)
      State(name, store, heap, model)
    }

    // other states
    val others = state
      .oldHeaps
      .filter { case (name, _) => name != "old" && !label.contains(name) }
      .map { case (name, siliconHeap) =>
        val heap = buildHeap(siliconHeap, partitions)
        State(name, store, heap, model)
      }
      .toSeq

    (current, others)
  }

  /**
    * Returns an abstraction of the given state for the given instance.
    *
    * @param state    The state to abstract.
    * @param instance The instance (used for the atomic predicates).
    * @return The abstracted state.
    */
  private def abstractState(state: State, instance: Instance): Abstraction = {
    val label = state.name
    val atoms = instance.formalAtoms
    val values = atoms
      .zipWithIndex
      .map { case (atom, index) =>
        val name = s"${label}_$index"
        val term = state.store(name)
        atom -> state.evaluateBoolean(term)
      }
      .toMap
    Abstraction(values)
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
        val name = variable.name
        val value = partitions.find(term)
        name -> value
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
    * A state extracted from the silicon verifier.
    *
    * @param name  The name identifying the state.
    * @param store The store map.
    * @param heap  The heap map.
    * @param model The model.
    */
  private case class State(name: String, store: Map[String, Term], heap: Map[Term, Map[String, Term]], model: Model) {
    /**
      * Evaluates the given silver expression to a silicon term.
      *
      * @param expression The expression to evaluate.
      * @return The resulting term.
      */
    def toTerm(expression: sil.Exp): Term = expression match {
      case sil.LocalVar(name, _) => store(name)
      case sil.FieldAccess(receiver, field) => heap(toTerm(receiver))(field.name)
    }

    def evaluateBoolean(term: Term): Boolean = term match {
      case terms.True() => true
      case terms.False() => false
      case terms.Not(argument) => !evaluateBoolean(argument)
      case terms.Equals(left, right) => left.sort match {
        case terms.sorts.Ref => evaluateReference(left) == evaluateReference(right)
      }
      case _ => ???
    }

    def evaluatePermission(term: Term): Double = term match {
      case terms.NoPerm() => 0.0
      case terms.FullPerm() => 1.0
      case terms.Ite(condition, left, right) =>
        if (evaluateBoolean(condition)) evaluatePermission(left)
        else evaluatePermission(right)
      case _ => ???
    }

    def evaluateReference(term: Term): String = term match {
      case terms.Var(identifier, _) => readModel(identifier.name)
      case terms.Null() => readModel(name = "$Ref.null")
      case _ => ???
    }

    def readModel(name: String): String =
      model.entries(name) match {
        case SingleEntry(value) => value
      }
  }

  private case class Adaptor(current: State, target: State, instance: Instance) {
    /**
      * The reachability map.
      *
      * TODO: Number of steps.
      */
    private val reachability = recurse(initial, steps = 3)

    def adapt(expression: sil.Exp): Set[sil.Exp] =
      expression match {
        case _: sil.LocalVar | _: sil.FieldAccess => adaptPath(expression)
        case _: sil.NullLit => Set(expression)
        case sil.EqCmp(left, right) => for (l <- adapt(left); r <- adapt(right)) yield sil.EqCmp(l, r)()
        case sil.NeCmp(left, right) => for (l <- adapt(left); r <- adapt(right)) yield sil.NeCmp(l, r)()
      }

    def adaptLocation(location: sil.LocationAccess): Set[sil.LocationAccess] =
      location match {
        case sil.FieldAccess(receiver, field) =>
          adapt(receiver).map { adapted => sil.FieldAccess(adapted, field)() }
        case sil.PredicateAccess(arguments, name) =>
          Collections
            .product(arguments.map { argument => adapt(argument) })
            .map { combination => sil.PredicateAccess(combination, name)() }
      }

    def adaptState(state: Abstraction): Abstraction = {
      val values = state.values.flatMap { case (atom, value) =>
        adapt(atom).map { adapted => adapted -> value }
      }
      Abstraction(values)
    }

    /**
      * Adapts the access path represented by the given expression.
      *
      * @param path The path to adapt.
      * @return The set of expressions describing the given path in the target state.
      */
    private def adaptPath(path: sil.Exp): Set[sil.Exp] = {
      val term = target.toTerm(path)
      reachability
        .getOrElse(term, Set.empty)
        .map { adapted => instance.toFormal(adapted) }
    }

    /**
      * Returns the reachability map of everything that is directly reachable from the store of the state.
      *
      * @return The initial reachability map.
      */
    private def initial: Map[Term, Set[sil.Exp]] = {
      val empty = Map.empty[Term, Set[sil.Exp]]
      current
        .store
        .filterKeys { name => name.startsWith(target.name) }
        .foldLeft(empty) {
          case (result, (name, value)) =>
            val variable = sil.LocalVar(name.drop(target.name.length + 1), sil.Ref)()
            val set = result.getOrElse(value, Set.empty) + variable
            result.updated(value, set)
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
            current.heap.getOrElse(term, Map.empty).foldLeft(map1) {
              case (map2, (name, value)) =>
                val field = sil.Field(name, sil.Ref)()
                val extended = paths.map { path => sil.FieldAccess(path, field)() }
                val set = map2.getOrElse(value, Set.empty) ++ extended
                map2.updated(value, set)
            }
        }
        // recurse and combine results
        Collections.combine[Term, Set[sil.Exp]](map, recurse(next, steps - 1), _ ++ _)
      }
  }

}
