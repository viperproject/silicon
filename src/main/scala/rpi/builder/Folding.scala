package rpi.builder

import rpi.Names
import rpi.inference.context.Context
import rpi.inference.Hypothesis
import rpi.inference.annotation.Annotation
import rpi.util.ast.Expressions._
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

  // TODO: Incorporate into annotation info.
  var old: Option[String] = None

  /**
    * Unfolds the given expression up to the maximal depth.
    *
    * @param expression The expression to unfold.
    * @param guards     The guards collected so far.
    * @param maxDepth   The maximal depth.
    * @param hypothesis The current hypothesis.
    * @param default    The default action for leaf expressions.
    */
  protected def unfold(expression: ast.Exp, guards: Seq[ast.Exp] = Seq.empty)
                      (implicit maxDepth: Int, hypothesis: Hypothesis,
                       default: (ast.Exp, Seq[ast.Exp]) => Unit = (_, _) => ()): Unit =
    expression match {
      case ast.And(left, right) =>
        unfold(left, guards)
        unfold(right, guards)
      case ast.Implies(guard, guarded) =>
        unfold(guarded, guards :+ guard)
      case predicate@ast.PredicateAccessPredicate(access, _) =>
        val depth = getDepth(access.args.head)
        if (depth < maxDepth) {
          val unfolds = makeScope {
            // unfold predicate
            addUnfold(predicate)
            // recursively unfold predicates appearing in body
            val instance = context.instance(predicate.loc)
            val body = hypothesis.getPredicateBody(instance)
            unfold(body)
          }
          addConditional(guards, unfolds)
        } else default(predicate, guards)
      case other =>
        default(other, guards)
    }

  /**
    * Folds the given expression from the maximal depth.
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
    * @param expression  The expression to fold.
    * @param annotations The annotations.
    * @param maxDepth    The maximal depth.
    * @param hypothesis  The current hypothesis.
    * @param default     The default action for leaf expressions.
    */
  protected def foldWithAnnotations(expression: ast.Exp, annotations: Seq[Annotation])
                                   (implicit maxDepth: Int, hypothesis: Hypothesis,
                                    default: (ast.Exp, Seq[ast.Exp]) => Unit = (_, _) => ()): Unit = {
    /**
      * Returns the condition that the given current argument is relevant for an annotation with the given name.
      *
      * @param name    The name of the annotation.
      * @param current The current argument.
      * @return The condition.
      */
    def getCondition(name: String, current: ast.Exp): ast.Exp = {
      val equalities = annotations.map {
        case Annotation(`name`, argument) =>
          makeEquality(current, argument)
      }
      makeOr(equalities)
    }

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
              val body = makeScope {
                // down condition
                val condition = getCondition(Names.downAnnotation, end)
                // conditionally apply lemma
                val thenBody = makeScope {
                  // get lemma instance
                  val instance = {
                    val previous = ast.LocalVar(s"${old.get}_${end.name}", ast.Ref)()
                    val arguments = Seq(start, previous, end)
                    context.instance(Names.appendLemma, arguments)
                  }
                  // fold lemma precondition
                  val precondition = hypothesis.getLemmaPrecondition(instance)
                  handleStart(precondition)
                  // apply lemma
                  val lemmaApplication = hypothesis.getLemmaApplication(instance)
                  addStatement(lemmaApplication)
                }
                val elseBody = makeScope(handleStart(predicate))
                addConditional(condition, thenBody, elseBody)
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
          val body = makeScope {
            // down condition
            val start = predicate.loc.args.head
            val condition = getCondition(Names.downAnnotation, start)
            // conditionally decrease the maximal fold depth
            val thenBranch = makeScope(fold(predicate)(maxDepth - 1, hypothesis, default))
            val elseBranch = makeScope(fold(predicate))
            addConditional(condition, thenBranch, elseBranch)
          }
          addConditional(guards, body)
        case other =>
          fold(other, guards)
      }

    if (annotations.isEmpty) fold(expression)
    else handleEnd(expression)
  }
}
