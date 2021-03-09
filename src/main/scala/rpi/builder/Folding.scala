package rpi.builder

import rpi.Names
import rpi.inference.context.Context
import rpi.inference.Hypothesis
import rpi.inference.annotation.Hint
import rpi.util.ast.Expressions._
import rpi.util.ast.Statements._
import rpi.util.ast.ValueInfo
import viper.silver.ast

/**
  * Mixin providing methods to unfold and fold specifications.
  */
trait Folding extends ProgramBuilder {
  /**
    * The context.
    */
  protected def context: Context

  /**
    * Unfolds the given expression up to the maximal depth.
    *
    * NOTE: The default action function is used by the query builder as a hook to track unfolded field accesses.
    *
    * @param expression The expression to unfold.
    * @param outer      The outer guards (already handled by conditionals)
    * @param guards     The current guards (not yet handled by conditionals)
    * @param maxDepth   The maximal depth.
    * @param hypothesis The current hypothesis.
    * @param default    The default action for leaf expressions.
    */
  protected def unfold(expression: ast.Exp, outer: Seq[ast.Exp] = Seq.empty, guards: Seq[ast.Exp] = Seq.empty)
                      (implicit maxDepth: Int, hypothesis: Hypothesis,
                       default: (ast.Exp, Seq[ast.Exp], Seq[ast.Exp]) => Unit = (_, _, _) => ()): Unit =
    expression match {
      case ast.And(left, right) =>
        unfold(left, outer, guards)
        unfold(right, outer, guards)
      case ast.Implies(guard, guarded) =>
        unfold(guarded, outer, guards :+ guard)
      case predicate@ast.PredicateAccessPredicate(access, _) =>
        val depth = getDepth(access.args.head)
        if (depth < maxDepth) {
          val unfolds = makeScope {
            // unfold predicate
            addUnfold(predicate)
            // recursively unfold predicates appearing in body
            val instance = context.instance(predicate.loc)
            val body = hypothesis.getPredicateBody(instance)
            unfold(body, outer ++ guards)
          }
          addConditional(guards, unfolds)
        } else default(predicate, outer, guards)
      case other =>
        default(other, outer, guards)
    }

  /**
    * Folds the given expression from the maximal depth.
    *
    * NOTE: The default action function is used by the query builder to save permissions to folded fields and predicate
    * accesses.
    *
    * @param expression The expression to fold.
    * @param guards     The guards collected so far.
    * @param maxDepth   The maximal depth.
    * @param hypothesis The current hypothesis.
    * @param default    THe default action for leaf expressions.
    */
  protected def fold(expression: ast.Exp, guards: Seq[ast.Exp] = Seq.empty)
                    (implicit maxDepth: Int, hypothesis: Hypothesis,
                     default: (ast.Exp, Seq[ast.Exp]) => Unit = (_, _) => ()): Unit =
    expression match {
      case ast.And(left, right) =>
        fold(left, guards)
        fold(right, guards)
      case ast.Implies(guard, guarded) =>
        fold(guarded, guards :+ guard)
      case predicate@ast.PredicateAccessPredicate(access, _) =>
        val depth = getDepth(access.args.head)
        if (depth < maxDepth) {
          val folds = makeScope {
            // recursively fold predicates appearing in body
            val instance = context.instance(predicate.loc)
            val body = hypothesis.getPredicateBody(instance)
            fold(body)
            // fold predicate
            val info = ValueInfo(instance)
            addFold(predicate, info)
          }
          addConditional(guards, folds)
        } else default(predicate, guards)
      case other =>
        default(other, guards)
    }

  /**
    * Folds the given expression from the maximal depth under the consideration of the given annotations.
    *
    * @param expression The expression to fold.
    * @param hints      The annotations.
    * @param maxDepth   The maximal depth.
    * @param hypothesis The current hypothesis.
    * @param default    The default action for leaf expressions.
    */
  protected def foldWithAnnotations(expression: ast.Exp, hints: Seq[Hint])
                                   (implicit maxDepth: Int, hypothesis: Hypothesis,
                                    default: (ast.Exp, Seq[ast.Exp]) => Unit = (_, _) => ()): Unit = {
    val downs = hints.filter { hint => hint.isDown }

    /**
      * Handles the end argument of predicate instances appearing of the given expression.
      *
      * @param expression The expression.
      * @param guards     The guards collected so far.
      */
    def handleEnd(expression: ast.Exp, guards: Seq[ast.Exp] = Seq.empty): Unit =
      expression match {
        case ast.And(left, right) =>
          handleEnd(left, guards)
          handleEnd(right, guards)
        case ast.Implies(guard, guarded) =>
          handleEnd(guarded, guards :+ guard)
        case predicate: ast.PredicateAccessPredicate =>
          val arguments = predicate.loc.args
          arguments match {
            case Seq(start, end: ast.LocalVar) =>
              val body = {
                val without: ast.Stmt = makeScope(handleStart(predicate))
                downs.foldRight(without) {
                  case (hint, result) =>
                    // condition for lemma application
                    val condition = {
                      val equality = makeEquality(end, hint.argument)
                      makeAnd(hint.conditions :+ equality)
                    }
                    // create lemma application
                    val application = makeScope {
                      // get lemma instance
                      val arguments = Seq(start, hint.old, end)
                      val instance = context.instance(Names.appendLemma, arguments)
                      // fold lemma precondition
                      val precondition = hypothesis.getLemmaPrecondition(instance)
                      handleStart(precondition)
                      // apply lemma
                      val lemmaApplication = hypothesis.getLemmaApplication(instance)
                      addStatement(lemmaApplication)
                    }
                    // create conditional lemma application
                    makeConditional(condition, application, result)
                }
              }
              addConditional(guards, body)
            case _ =>
              handleStart(predicate, guards)
          }
        case other =>
          fold(other, guards)
      }

    /**
      * Handles the start argument of predicate instances appearing in the given expression.
      *
      * @param expression The expression.
      * @param guards     The guards collected so far.
      */
    def handleStart(expression: ast.Exp, guards: Seq[ast.Exp] = Seq.empty): Unit =
      expression match {
        case ast.And(left, right) =>
          handleStart(left, guards)
          handleStart(right, guards)
        case ast.Implies(guard, guarded) =>
          handleStart(guarded, guards :+ guard)
        case predicate: ast.PredicateAccessPredicate =>
          val start = predicate.loc.args.head
          val body = {
            val without: ast.Stmt = makeScope(fold(predicate))
            hints.foldRight(without) {
              case (hint, result) =>
                // condition for hint relevance
                val condition = {
                  val equality = makeEquality(start, hint.argument)
                  makeAnd(hint.conditions :+ equality)
                }
                // conditionally adapt fold depth
                val depth = if (hint.isDown) maxDepth - 1 else maxDepth + 1
                val adapted = makeScope(fold(predicate)(depth, hypothesis, default))
                makeConditional(condition, adapted, result)
            }
          }
          addConditional(guards, body)
        case other =>
          fold(other, guards)
      }

    if (hints.isEmpty) fold(expression)
    else handleEnd(expression)
  }
}