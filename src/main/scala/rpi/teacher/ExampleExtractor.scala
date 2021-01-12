package rpi.teacher

import rpi.{Names, Settings}
import rpi.inference._
import rpi.teacher.state.{Adaptor, ModelEvaluator, Snapshot, StateEvaluator}
import viper.silicon.interfaces.SiliconRawCounterexample
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
    // get counter example and offending location
    val (counter, offending, Some(info)) = extractInformation[FramingInfo](error)

    // get label and instance
    val (label, instance) = {
      val heaps = counter.state.oldHeaps
      context
        .allSnapshots
        .filter { case (label, _) => heaps.contains(label) }
        .head
    }

    // get state abstraction
    val abstraction = {
      // get state and model
      val model = ModelEvaluator(counter.model)
      // create state and snapshot
      val state = StateEvaluator(Some(label), counter.state, model)
      val snapshot = Snapshot(instance, state)
      // compute abstraction
      snapshot.formalAbstraction
    }

    // create and return example
    val specification = instance.specification
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
    // get counter example, offending location, and context info
    val (counter, offending, info) = extractInformation[BasicInfo](error)

    // get state and model
    val siliconState = counter.state
    val model = ModelEvaluator(counter.model)

    // get state snapshots
    val (currentSnapshot, otherSnapshots) = {
      // gather all encountered state snapshots
      val encountered = context
        .allSnapshots
        .flatMap { case (label, instance) =>
          if (siliconState.oldHeaps.contains(label)) {
            //Snapshot(label, instance, state, evaluator)
            val encounteredState = StateEvaluator(Some(label), siliconState, model)
            val snapshot = Snapshot(instance, encounteredState)
            Some(snapshot)
          } else None
        }

      // return current and all other state snapshots
      if (info.isDefined) {
        val current = Some(encountered.last)
        val others = encountered.init
        (current, others)
      } else {
        val current = None
        (current, encountered)
      }
    }

    // failing state
    val failState = currentSnapshot match {
      case Some(snapshot) => snapshot.state
      case None => StateEvaluator(None, siliconState, model)
    }

    // get current location
    val currentLocation = info match {
      case Some(BasicInfo(_, instance)) =>
        if (Settings.inline && !Names.isPredicate(instance.name)) offending
        else instance.toActual(offending)
      case _ => offending
    }

    // lazily compute current record
    lazy val currentRecord = currentSnapshot
      .map { currentSnapshot =>
        // abstraction
        val abstraction = {
          val currentAbstraction = currentSnapshot.formalAbstraction
          otherSnapshots.foldLeft(currentAbstraction) {
            case (combined, otherSnapshot) =>
              val adaptor = Adaptor(otherSnapshot.state, currentSnapshot)
              val otherAbstraction = otherSnapshot.actualAbstraction
              val adapted = adaptor.adaptAbstraction(otherAbstraction)
              combined.meet(adapted)
          }
        }
        // locations
        val locations = {
          val adaptor = Adaptor(failState, currentSnapshot)
          adaptor.adaptLocation(currentLocation)
        }
        // create record
        val specification = currentSnapshot.specification
        Record(specification, abstraction, locations)
      }

    // lazily compute all other records
    lazy val otherRecords = otherSnapshots
      .map { otherSnapshot =>
        // adaptor
        val adaptor = Adaptor(failState, otherSnapshot)
        // abstraction
        val abstraction = {
          val otherAbstraction = otherSnapshot.formalAbstraction
          currentSnapshot.foldLeft(otherAbstraction) {
            case (combined, currentSnapshot) =>
              val currentAbstraction = currentSnapshot.actualAbstraction
              val adapted = adaptor.adaptAbstraction(currentAbstraction)
              combined.meet(adapted)
          }
        }
        // create record
        val specification = otherSnapshot.specification
        val locations = adaptor.adaptLocation(currentLocation)
        Record(specification, abstraction, locations)
      }

    // create example
    val example = currentRecord match {
      case Some(currentRecord) =>
        // evaluate permission amount
        val permission = {
          val snapshot = currentSnapshot.get
          val name = context.getName(snapshot.label, currentLocation)
          snapshot.state.evaluatePermission(name)
        }
        // we want to require the missing permission form an upstream specification,
        // unless we previously already held some permission for the location
        if (permission == 0) ImplicationExample(currentRecord, otherRecords)
        else NegativeExample(currentRecord)
      case None => PositiveExample(otherRecords)
    }
    example
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
}