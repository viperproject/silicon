package rpi.teacher.state

import viper.silicon.state.terms
import viper.silicon.state.terms.{Term, sorts}
import viper.silver.verifier.{ApplicationEntry, ConstantEntry, Model, ModelEntry}

/**
  * A helper class used to evaluate a given model.
  *
  * @param model The model.
  */
case class ModelEvaluator(model: Model) {
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
        getEntry(identifier.name) match {
          case ConstantEntry(value) => value.toDouble
        }
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
    evaluate(term) match {
      case ConstantEntry(value) => value
    }

  /**
    * Evaluates the given term to a model entry.
    *
    * @param term The term to evaluate.
    * @return The model entry.
    */
  private def evaluate(term: Term): ModelEntry =
    term match {
      case terms.Null() =>
        getEntry(key = "$Ref.null")
      case terms.Var(identifier, _) =>
        getEntry(identifier.name)
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
    }

  /**
    * Returns the model entry associated with the given key.
    * @param key The key of the model entry.
    * @return The model entry.
    */
  private def getEntry(key: String): ModelEntry =
    model.entries(key)
}
