// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package rpi.inference.teacher.state

import viper.silicon.state.terms
import viper.silicon.state.terms.{Term, sorts}
import viper.silver.verifier._

/**
  * A helper class used to evaluate a given model.
  *
  * @param model The model.
  */
case class ModelEvaluator(model: Model) {
  /**
    * The map from snapshots to reference values used to evaluate wrapped snapshots.
    */
  private lazy val snapshots =
    getEntry(key = "$SortWrappers.$SnapTo$Ref") match {
      case MapEntry(options, default) => options
        .map { case (Seq(snapshot), value) => snapshot -> value.toString }
        .withDefaultValue(default.toString)
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
      case terms.Var(identifier, _) =>
        val value = getString(identifier.name)
        value.toBoolean
      case terms.Not(argument) =>
        !evaluateBoolean(argument)
      case terms.Equals(left, right) =>
        left.sort match {
          case sorts.Ref =>
            val leftValue = evaluateReference(left)
            val rightValue = evaluateReference(right)
            leftValue == rightValue
        }
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
      case terms.Var(identifier, _) =>
        val value = getString(identifier.name)
        value.toDouble
      case terms.PermPlus(left, right) =>
        val leftValue = evaluatePermission(left)
        val rightValue = evaluatePermission(right)
        leftValue + rightValue
      case terms.Ite(condition, left, right) =>
        val value = evaluateBoolean(condition)
        if (value) evaluatePermission(left)
        else evaluatePermission(right)
    }

  /**
    * Evaluates the given term to a reference (represented as a string).
    *
    * @param term The term to evaluate.
    * @return The reference value.
    */
  def evaluateReference(term: Term): String =
    term match {
      case terms.Null() =>
        getString(key = "$Ref.null")
      case terms.Var(identifier, _) =>
        getString(identifier.name)
      case terms.SortWrapper(wrapped, _) =>
        wrapped.sort match {
          case sorts.Snap =>
            val wrappedValue = evaluateSnapshot(wrapped)
            snapshots(wrappedValue)
        }
    }

  /**
    * Evaluates the given term to a heap snapshot (represented as a value entry).
    *
    * @param term The term to evaluate.
    * @return The snapshot value.
    */
  private def evaluateSnapshot(term: Term): ValueEntry =
    term match {
      case terms.Var(identifier, _) =>
        getValue(identifier.name)
      case terms.First(combined) =>
        val combinedValue = evaluateSnapshot(combined)
        combinedValue match {
          case ApplicationEntry(_, Seq(first, _)) => first
        }
      case terms.Second(combined) =>
        val combinedValue = evaluateSnapshot(combined)
        combinedValue match {
          case ApplicationEntry(_, Seq(_, second)) => second
        }
    }

  /**
    * Returns the model entry associated with the given key as a string value.
    *
    * @param key The key of the model entry.
    * @return The value.
    */
  private def getString(key: String): String =
    getEntry(key) match {
      case ConstantEntry(value) => value
    }

  /**
    * Returns the value entry associated with the given key.
    *
    * @param key The key of the model entry.
    * @return The value entry.
    */
  private def getValue(key: String): ValueEntry =
    getEntry(key) match {
      case value: ValueEntry => value
    }

  /**
    * Returns the model entry associated with the given key.
    * @param key The key of the model entry.
    * @return The model entry.
    */
  private def getEntry(key: String): ModelEntry =
    model.entries(key)
}
