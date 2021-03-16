// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package rpi.inference.teacher

import com.typesafe.scalalogging.LazyLogging
import rpi.Names
import rpi.inference.context.Instance
import rpi.inference._
import rpi.inference.teacher.query.Query
import rpi.inference.teacher.state._
import rpi.util.ast.Expressions.{makeField, makePredicate}
import rpi.util.ast.{Infos, Previous}
import viper.silicon.interfaces.SiliconRawCounterexample
import viper.silver.ast
import viper.silver.verifier._
import viper.silver.verifier.reasons.InsufficientPermission

/**
  * Extracts samples from verification errors.
  */
trait SampleExtractor extends AbstractTeacher with LazyLogging {
  /**
    * Type shortcut for counter examples.
    */
  private type Counter = SiliconRawCounterexample

  /**
    * Extracts a sample from the given verification error corresponding to a self-framing check.
    *
    * @param error The verification error.
    * @param query The query that caused the error.
    * @return The extracted sample.
    */
  def framingSample(error: VerificationError, query: Query): Sample = {
    logger.info(error.toString)

    // get counter example and offending location
    val (counter, offending, Some(location)) = extractInformation[ast.LocationAccess](error)

    // get label and instance
    val (label, instance) = {
      val heaps = counter.state.oldHeaps
      query
        .snapshots
        .filter { case (label, _) => heaps.contains(label) }
        .head
    }

    // get state abstraction
    // TODO: Debug abstraction
    val abstraction = {
      // get state and model
      val model = ModelEvaluator(counter.model)
      // create state and snapshot
      val state = StateEvaluator(Some(label), counter.state, model)
      val snapshot = Snapshot(instance, state)
      // compute abstraction
      val primary = snapshot.formalAtomicAbstraction
      // debug abstraction
      val secondary = SnapshotAbstraction(snapshot)
      DebugAbstraction(primary, secondary)
    }

    // create and return sample
    val specification = instance.specification
    val left = Record(specification, abstraction, Set(location))
    val right = Record(specification, abstraction, Set(offending))
    ImplicationSample(left, Seq(right))
  }

  /**
    * Extracts a sample from the given verification error corresponding to a basic check.
    *
    * @param error The verification error.
    * @param query The query that caused the error.
    * @return The extracted sample.
    */
  def basicSample(error: VerificationError, query: Query): Sample = {
    logger.info(error.toString)

    // get counter example, offending location, and context info
    val (counter, offending, info) = extractInformation[Instance](error)

    // get state and model
    val siliconState = counter.state
    val model = ModelEvaluator(counter.model)

    // get state snapshots
    val (currentSnapshot, otherSnapshots) = {
      // gather all encountered state snapshots
      val encountered = query
        .snapshots
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
      case Some(instance) =>
        if (configuration.noInlining() || Names.isRecursive(instance.name)) instance.toActual(offending)
        else offending
      case _ => offending
    }

    // lazily compute current record
    lazy val currentRecord = currentSnapshot
      .map { currentSnapshot =>
        // abstraction
        val abstraction = {
          val currentAbstraction = currentSnapshot.formalAtomicAbstraction
          otherSnapshots.foldLeft(currentAbstraction) {
            case (combined, otherSnapshot) =>
              val adaptor = Adaptor(otherSnapshot.state, currentSnapshot)
              val otherAbstraction = otherSnapshot.actualAtomicAbstraction
              val adapted = adaptor.adaptAbstraction(otherAbstraction)
              combined.meet(adapted)
          }
        }
        // locations
        val locations = {
          // check whether variable was used to save an expression

          def bar(x: ast.Exp): ast.Exp =
            x match {
              case variable: ast.LocalVar =>
                val info = variable.info.getUniqueInfo[Previous]
                info match {
                  case Some(Previous(value)) => value
                  case _ => variable
                }
              case ast.FieldAccess(receiver, field) =>
                makeField(bar(receiver), field)
              case _ =>
                x
            }

          def foo(access: ast.LocationAccess): ast.LocationAccess =
            access match {
              case ast.FieldAccess(receiver, field) =>
                makeField(bar(receiver), field)
              case ast.PredicateAccess(arguments, name) =>
                val x = arguments.map { argument => bar(argument) }
                makePredicate(name, x)
            }

          val x = foo(currentLocation)

          val adaptor = Adaptor(failState, currentSnapshot)
          adaptor.adaptLocation(x)
        }
        // create record
        val specification = currentSnapshot.specification
        // TODO: Eventually replace with partition abstraction.
        // inject snapshot abstraction for debug purposes
        val debug = {
          val secondary = SnapshotAbstraction(currentSnapshot)
          DebugAbstraction(abstraction, secondary)
        }
        Record(specification, debug, locations)
      }

    // lazily compute all other records
    lazy val otherRecords = otherSnapshots
      .map { otherSnapshot =>
        // adaptor
        val adaptor = Adaptor(failState, otherSnapshot)
        // abstraction
        val abstraction = {
          val otherAbstraction = otherSnapshot.formalAtomicAbstraction
          currentSnapshot.foldLeft(otherAbstraction) {
            case (combined, currentSnapshot) =>
              val currentAbstraction = currentSnapshot.actualAtomicAbstraction
              val adapted = adaptor.adaptAbstraction(currentAbstraction)
              combined.meet(adapted)
          }
        }
        // create record
        val specification = otherSnapshot.specification
        val locations = adaptor.adaptLocation(currentLocation)
        // TODO: Eventually replace with partition abstraction.
        // inject snapshot abstraction for debug purposes
        val debug = {
          val secondary = SnapshotAbstraction(otherSnapshot)
          DebugAbstraction(abstraction, secondary)
        }
        Record(specification, debug, locations)
      }

    // create sample
    val sample = currentRecord match {
      case Some(currentRecord) =>
        // evaluate permission amount
        val permission = {
          val snapshot = currentSnapshot.get
          val name = query.name(snapshot.label, currentLocation)
          snapshot.state.evaluatePermission(name)
        }
        // we want to require the missing permission form an upstream specification,
        // unless we previously already held some permission for the location
        if (permission == 0) ImplicationSample(currentRecord, otherRecords)
        else NegativeSample(currentRecord)
      case None => PositiveSample(otherRecords)
    }
    sample
  }

  /**
    * Extracts information from the given verification error. The information consists of the counter example, the
    * offending location, and some context information (if available).
    *
    * @param error The verification error.
    * @tparam T The type of the context information.
    * @return The extracted information.
    */
  private def extractInformation[T](error: VerificationError): (Counter, ast.LocationAccess, Option[T]) = {
    // extract counter example
    val counter = error.counterexample match {
      case Some(value: Counter) => value
      case _ => sys.error("Verification error does not contain a counter example.")
    }
    // extract offending location
    val offending = error.reason match {
      case InsufficientPermission(location) => location
      case reason => sys.error(s"Unexpected reason: $reason")
    }
    // extract context info
    val info = error.offendingNode match {
      case node: ast.Infoed => Infos.valueOption[T](node)
      case _ => None
    }
    // return information
    (counter, offending, info)
  }
}
