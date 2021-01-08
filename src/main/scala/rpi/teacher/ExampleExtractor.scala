package rpi.teacher

import rpi.{Names, Settings}
import rpi.inference._
import rpi.util.{Collections, UnionFind}
import viper.silicon.interfaces.SiliconRawCounterexample
import viper.silicon.state._
import viper.silicon.state.terms.Term
import viper.silver.ast
import viper.silver.verifier._
import viper.silver.verifier.reasons.InsufficientPermission

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
    ImplicationExample(left, Seq(right))
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

    // get current location
    val currentLocation = info match {
      case Some(BasicInfo(_, instance)) =>
        if (Settings.inline && !Names.isPredicate(instance.name)) offending
        else instance.toActual(offending)
      case _ => offending
    }

    // build current and other states
    val (currentState, otherStates) = {
      // get silicon state, get model, and build partitions
      val siliconState = counter.state
      val model = counter.model
      val partitions = buildPartitions(counter)

      // build store
      val store = {
        val siliconStore = siliconState.g
        buildStore(siliconStore, partitions)
      }

      // build all encountered states
      val encountered = {
        val heapMap = siliconState.oldHeaps
        context
          .allLabels
          .flatMap { label =>
            heapMap
              .get(label)
              .map { siliconHeap =>
                val heap = buildHeap(siliconHeap, partitions)
                State(label, store, heap, model)
              }
          }
      }

      // build current state if necessary and return states
      if (label.isDefined) {
        // the last encountered state is the current state
        val current = encountered.last
        val others = encountered.init
        (current, others)
      } else {
        // build current state in case it has not been encountered
        val siliconHeap = siliconState.h
        val heap = buildHeap(siliconHeap, partitions)
        val current = State("current", store, heap, model)
        (current, encountered)
      }
    }

    val currentTriples = label
      .map { label =>
        val instance = context.getExhaled(label)
        val abstraction = abstractState(currentState, instance)
        (currentState, instance, abstraction)
      }

    val otherTriples = otherStates
      .map { state =>
        val instance = context.getInstance(state.label)
        val abstraction = abstractState(state, instance)
        (state, instance, abstraction)
      }

    lazy val currentRecords = currentTriples
      .map { case (currentState, currentInstance, currentAbstraction) =>
        // reachability
        val currentReachability = Reachability(currentState, currentInstance)
        // refine abstraction with information from other states
        val abstraction = otherTriples.foldLeft(currentAbstraction) {
          case (combined, (otherState, otherInstance, otherAbstraction)) =>
            val adaptor = Adaptor(otherState, currentReachability)
            val actual = otherInstance.toActual(otherAbstraction)
            val adapted = adaptor.adaptState(actual)
            combined.meet(adapted)
        }
        // create record
        val specification = currentInstance.specification
        val locations = {
          // Slight abuse of adaptor to compute reachability in current state
          val adaptor = Adaptor(currentState, currentReachability)
          adaptor.adaptLocation(currentLocation)
        }
        Record(specification, abstraction, locations)
      }

    lazy val otherRecords = otherTriples
      .map { case (otherState, otherInstance, otherAbstraction) =>
        // create adaptor
        val adaptor = {
          val otherReachability = Reachability(otherState, otherInstance)
          Adaptor(currentState, otherReachability)
        }
        // refine abstraction with information from current state
        val abstraction = currentTriples.foldLeft(otherAbstraction) {
          case (combined, (_, currentInstance, currentAbstraction)) =>
            val actual = currentInstance.toActual(currentAbstraction)
            val adapted = adaptor.adaptState(actual)
            combined.meet(adapted)
        }
        // create record
        val specification = otherInstance.specification
        val locations = adaptor.adaptLocation(currentLocation)
        Record(specification, abstraction, locations)
      }

    // create example
    currentRecords match {
      case Some(currentRecord) =>
        // evaluate permission amount
        val name = context.getName(label.get, currentLocation)
        val term = currentState.store(name)
        val permission = currentState.evaluatePermission(term)
        // we want to require the missing permission from an upstream specification,
        // unless we previously already held some permissions for the location
        if (permission == 0) ImplicationExample(currentRecord, otherRecords)
        else NegativeExample(currentRecord)
      case None => PositiveExample(otherRecords)
    }
  }

  /**
    * Extracts information from the given verification error. The information consists of the counter example, the
    * offending location, and some context information (if available).
    *
    * @param error The verification error.
    * @tparam T The type of the context information.
    * @return The extracted information.
    */
  private def extractInformation[T <: ContextInfo : ClassTag](error: VerificationError): (Counter, ast.LocationAccess, Option[T]) = {
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
      case node: ast.Infoed => node.info.getUniqueInfo[T]
      case _ => None
    }
    // return information
    (counter, offending, info)
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
    def toTerm(expression: ast.Exp): Term =
      expression match {
        case ast.LocalVar(variable, _) =>
          // look up the version of the variable corresponding to this state
          val name = if (label == "current") variable else s"${label}_$variable"
          store(name)
        case ast.FieldAccess(receiver, field) =>
          heap(toTerm(receiver))(field.name)
      }

    /**
      * Evaluates the given term to a boolean.
      *
      * @param term The term to evaluate.
      * @return The boolean value.
      */
    def evaluateBoolean(term: Term): Boolean =
      term match {
        case terms.True() => true
        case terms.False() => false
        case terms.Not(argument) => !evaluateBoolean(argument)
        case terms.Equals(left, right) => left.sort match {
          case terms.sorts.Ref => evaluateReference(left) == evaluateReference(right)
        }
        case _ => ???
      }

    /**
      * Evaluates the given term to a permission value (represented as a double).
      *
      * @param term The term to evaluate.
      * @return The permission value.
      */
    def evaluatePermission(term: Term): Double =
      term match {
        case terms.NoPerm() => 0.0
        case terms.FullPerm() => 1.0
        case terms.PermPlus(left, right) =>
          evaluatePermission(left) + evaluatePermission(right)
        case terms.Ite(condition, left, right) =>
          if (evaluateBoolean(condition)) evaluatePermission(left)
          else evaluatePermission(right)
        case _ => ???
      }

    /**
      * Evaluates the given term to a reference (represented as a string).
      *
      * @param term The term.
      * @return The reference value.
      */
    def evaluateReference(term: Term): String =
      evaluate(term) match {
        case ConstantEntry(value) => value
      }

    /**
      * Evaluates the given term to a value entry.
      *
      * @param term The term to evaluate.
      * @return The value entry.
      */
    private def evaluate(term: Term): ValueEntry =
      term match {
        case terms.Var(identifier, _) =>
          readModel(identifier.name)
        case terms.Null() =>
          readModel(key = "$Ref.null")
        case terms.SortWrapper(wrapped, _) =>
          evaluate(wrapped)
        case terms.First(pair) =>
          evaluate(pair) match {
            case ApplicationEntry(_, Seq(first, _)) => first
          }
        case terms.Second(pair) =>
          evaluate(pair) match {
            case ApplicationEntry(_, Seq(_, second)) => second
          }
        case _ => ???
      }

    /**
      * Reads the value entry with the given key from the model.
      *
      * @param key The key of the value.
      * @return The value.
      */
    private def readModel(key: String): ValueEntry =
      model.entries(key) match {
        case value: ValueEntry => value
      }

    override def toString: String = s"State($label, ...)"
  }

  private case class Adaptor(current: State, reachability: Reachability) {
    def adapt(expression: ast.Exp): Set[ast.Exp] =
      expression match {
        case _: ast.LocalVar | _: ast.FieldAccess => adaptPath(expression)
        case _: ast.NullLit => Set(expression)
        case ast.EqCmp(left, right) => for (l <- adapt(left); r <- adapt(right)) yield ast.EqCmp(l, r)()
        case ast.NeCmp(left, right) => for (l <- adapt(left); r <- adapt(right)) yield ast.NeCmp(l, r)()
      }

    def adaptLocation(location: ast.LocationAccess): Set[ast.LocationAccess] =
      location match {
        case ast.FieldAccess(receiver, field) =>
          adapt(receiver).map { adapted => ast.FieldAccess(adapted, field)() }
        case ast.PredicateAccess(arguments, name) =>
          Collections
            .product(arguments.map { argument => adapt(argument) })
            .map { combination => ast.PredicateAccess(combination, name)() }
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
    private def adaptPath(path: ast.Exp): Set[ast.Exp] = {
      val term = current.toTerm(path)
      reachability.get(term)
    }
  }

  /**
    * Computes reachability information that can be used to determine a set of expressions that evaluate to a given
    * term or expression.
    *
    * @param state    The state with respect to which the reachability information is computed.
    * @param instance The instance used to perform the actual-to-formal adaption.
    */
  private case class Reachability(state: State, instance: Instance) {
    /**
      * The reachability map that associates terms with with a set of expressions that are guaranteed to evaluate to
      * that term in the target state.
      *
      * TODO: Number of steps.
      */
    private val map = recurse(initial, steps = 3)

    def get(term: Term): Set[ast.Exp] =
      map.getOrElse(term, Set.empty)

    /**
      * Returns the reachability map of everything that is directly reachable from the store of the state.
      *
      * @return The initial reachability map.
      */
    private def initial: Map[Term, Set[ast.Exp]] =
      instance
        .arguments
        .zip(instance.parameters)
        .foldLeft(Map.empty[Term, Set[ast.Exp]]) {
          case (result, (argument, parameter)) =>
            val value = state.toTerm(argument)
            val existing = result.getOrElse(value, Set.empty)
            result.updated(value, existing + parameter)
        }

    /**
      * Updates the current reachability map by recursing the given number of steps.
      *
      * @param map   The current reachability map.
      * @param steps The number of steps.
      * @return The reachability map.
      */
    private def recurse(map: Map[Term, Set[ast.Exp]], steps: Int): Map[Term, Set[ast.Exp]] =
      if (steps == 0) map
      else {
        // compute next step of the reachability map
        val empty = Map.empty[Term, Set[ast.Exp]]
        val next = map.foldLeft(empty) {
          case (map1, (term, paths)) =>
            state.heap.getOrElse(term, Map.empty).foldLeft(map1) {
              case (map2, (name, value)) =>
                val field = ast.Field(name, ast.Ref)()
                val extended = paths.map { path => ast.FieldAccess(path, field)() }
                val set = map2.getOrElse(value, Set.empty) ++ extended
                map2.updated(value, set)
            }
        }
        // recurse and combine results
        Collections.combine[Term, Set[ast.Exp]](map, recurse(next, steps - 1), _ ++ _)
      }
  }

}
