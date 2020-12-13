package rpi.teacher

import rpi.inference._
import rpi.util.{Collections, UnionFind}
import viper.silicon.interfaces.SiliconRawCounterexample
import viper.silicon.state._
import viper.silicon.state.terms.Term
import viper.silver.verifier.{Model, SingleEntry, VerificationError}
import viper.silver.verifier.reasons.InsufficientPermission
import viper.silver.{ast => sil}

import scala.reflect.ClassTag

/**
  * Extracts examples from verification errors.
  *
  * @param teacher The pointer to the teacher.
  */
class ExampleExtractor(teacher: Teacher) {
  /**
    * Type shortcut for counter examples.
    */
  private type Counter = SiliconRawCounterexample

  /**
    * Returns the pointer to the inference.
    *
    * @return The pointer to the inference.
    */
  def inference: Inference = teacher.inference

  /**
    * Extracts an example from the given verification error corresponding to a self-framingness check.
    *
    * @param error   The verification error.
    * @param context The context object.
    * @return The extracted example.
    */
  def extractFraming(error: VerificationError, context: Context): Example = {
    println(error)
    // extract counter example and offending location
    val (counter, offending, Some(info)) = extractInformation[FramingInfo](error)


    val state = {
      val siliconState = counter.state
      val partitions = new UnionFind[Term]
      val model = counter.model

      val store = {
        val siliconStore = siliconState.g
        buildStore(siliconStore, partitions)
      }

      // get label
      val labels = siliconState
        .oldHeaps
        .flatMap {
          case (name, _) if context.isInhaled(name) => Some(name)
          case _ => None
        }
      assert(labels.size == 1)
      val label = labels.head

      // create state
      State(label, store, Map.empty, model)
    }

    val instance = context.getInhaled(state.label)
    val specification = instance.specification
    val abstraction = abstractState(state, instance)

    // create and return example
    val left = Record(specification, abstraction, Set(info.location))
    val right = Record(specification, abstraction, Set(offending))
    Implication(Seq(left), Seq(right))
  }

  /**
    * Extracts an example from the given verification error corresponding to a basic check.
    *
    * @param error   The verification error.
    * @param context The context object.
    * @return The extracted example.
    */
  def extractBasic(error: VerificationError, context: Context): Example = {
    println(error)
    // extract counter example, offending location, and context info
    // TODO: I don't like how the optional label is handled further down.
    val (counter, offending, info) = extractInformation[BasicInfo](error)
    val label = info.map(_.label)

    // extract states
    val (currentState, inhaledStates) = extractStates(counter, label, context)

    val currentLocation = info match {
      case Some(BasicInfo(_, instance)) => instance.toActual(offending)
      case _ => offending
    }

    lazy val preRecords =
      inhaledStates
        .map { inhaledState =>
          val inhaledInstance = context.getInhaled(inhaledState.label)
          val adaptor = Adaptor(currentState, inhaledState, inhaledInstance)
          val state =
            if (label.isDefined) {
              // combine information from pre and post state
              val currentInstance = context.getExhale(label.get)
              val pre = abstractState(inhaledState, inhaledInstance)
              val post = abstractState(currentState, currentInstance)
              val x = currentInstance.toActual(post)
              pre.meet(adaptor.adaptState(x))
            } else abstractState(inhaledState, inhaledInstance)
          // TODO: It could be beneficial to have a set of all equivalent locations.
          val locations = adaptor.adaptLocation(currentLocation)
          Record(inhaledInstance.specification, state, locations)
        }

    // post record
    lazy val postRecords = {
      val currentInstance = context.getExhale(label.get)
      val state = abstractState(currentState, currentInstance)
      val locations = Set(currentInstance.toFormal(currentLocation))
      val record = Record(currentInstance.specification, state, locations)
      Seq(record)
    }

    // create example
    if (label.isDefined) {
      // evaluate permission amount
      val name = context.getName(label.get, currentLocation)
      val term = currentState.store(name)
      val permission = currentState.evaluatePermission(term)
      // create implication or negative example depending on permission amount
      if (permission == 0) Implication(postRecords, preRecords)
      else Negative(postRecords)
    } else Positive(preRecords)
  }

  /**
    * Extracts information from the given verification error. The information consists of the counter example, the
    * offending location, and some context information (if available).
    *
    * @param error The verification error.
    * @tparam T The type of the context information.
    * @return The extracted information.
    */
  private def extractInformation[T <: ContextInfo : ClassTag](error: VerificationError): (Counter, sil.LocationAccess, Option[T]) = {
    // extract counter example
    val counter = error.counterexample match {
      case Some(value: Counter) => value
      case _ => ??? // should not happen
    }
    // extract offending location
    val offending = error.reason match {
      case InsufficientPermission(location) => location
      case _ => ??? // should not happen
    }
    // extract context info
    val info = error.offendingNode match {
      case node: sil.Infoed => node.info.getUniqueInfo[T]
      case _ => None
    }
    // return information
    (counter, offending, info)
  }

  /**
    * Extracts states from the given counter example.
    *
    * @param counter The counter example.
    * @param context The context provided by the check builder.
    * @return A tuple holding the current state and a sequence of states that precede the current state where some
    *         specifications were inhaled.
    */
  private def extractStates(counter: Counter, label: Option[String], context: Context): (State, Seq[State]) = {
    // get silicon state, partitions, and model
    val siliconState = counter.state
    val partitions = buildPartitions(counter)
    val model = counter.model

    // build store
    // TODO: Restrict stores?
    val store = {
      val siliconStore = siliconState.g
      buildStore(siliconStore, partitions)
    }

    // build current state
    val state = {
      val (name, siliconHeap) = label match {
        case Some(existing) => (existing, siliconState.oldHeaps(existing))
        case None => ("current", siliconState.h)
      }
      val heap = buildHeap(siliconHeap, partitions)
      State(name, store, heap, model)
    }

    // build inhaled states
    val inhaled = siliconState
      .oldHeaps
      .flatMap {
        case (name, siliconHeap) if context.isInhaled(name) =>
          val heap = buildHeap(siliconHeap, partitions)
          Some(State(name, store, heap, model))
        case _ => None
      }
      .toSeq

    // return states
    (state, inhaled)
  }

  /**
    * Builds the partitions representing equivalent terms.
    * TODO: This might be replaced by evaluating the model?
    *
    * @param counter The counter example.
    * @return The partitions.
    */
  private def buildPartitions(counter: Counter): UnionFind[Term] = {
    // initialize data structure
    val partitions = new UnionFind[Term]
    // unify equivalent terms
    counter
      .conditions
      .foreach {
        case terms.BuiltinEquals(left, right) =>
          partitions.union(left, right)
        case _ => // do nothing
      }
    // return partitions
    partitions
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
    * Returns an abstraction of the given state for the given instance.
    *
    * @param state    The state to abstract.
    * @param instance The instance (used for the atomic predicates).
    * @return The abstracted state.
    */
  private def abstractState(state: State, instance: Instance): Abstraction = {
    val label = state.label
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
    * A state extracted from the silicon verifier.
    *
    * @param label The label identifying the state.
    * @param store The store map.
    * @param heap  The heap map.
    * @param model The model.
    */
  private case class State(label: String, store: Map[String, Term], heap: Map[Term, Map[String, Term]], model: Model) {
    /**
      * Evaluates the given silver expression to a silicon term.
      *
      * @param expression The expression to evaluate.
      * @return The resulting term.
      */
    def toTerm(expression: sil.Exp): Term = expression match {
      case sil.LocalVar(variable, _) => store(variable)
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
      * The reachability map that associates terms with with a set of expressions that are guaranteed to evaluate to
      * that term in the target state.
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
      val values = state
        .values
        .flatMap { case (atom, value) =>
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
      val term = current.toTerm(path)
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
      target
        .store
        .filterKeys { name => name.startsWith(target.label) }
        .foldLeft(empty) {
          case (result, (name, value)) =>
            val variable = sil.LocalVar(name.drop(target.label.length + 1), sil.Ref)()
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
            target.heap.getOrElse(term, Map.empty).foldLeft(map1) {
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
