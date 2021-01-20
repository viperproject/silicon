package rpi.teacher

import rpi.{Names, Settings}
import viper.silver.ast

import scala.annotation.tailrec

case class Check(statements: Seq[ast.Stmt]) {
  /**
    * The depth up to which specifications should be unfolded.
    *
    * Note: Ths is a very crude approximation.
    */
  lazy val unfoldDepth: Int = {
    /**
      * Computes the unfold depth for the given node.
      *
      * @param node The node.
      * @return The unfold depth.
      */
    def depth(node: ast.Node): Int =
      node match {
        case ast.Seqn(statements, _) =>
          maxDepth(statements)
        case ast.If(condition, thenBranch, elseBranch) =>
          maxDepth(Seq(condition, thenBranch, elseBranch))
        case _: ast.While => 0
        case ast.Inhale(condition) =>
          if (condition.isPure) depth(condition) else 0
        case ast.Exhale(condition) =>
          if (condition.isPure) depth(condition) else 0
        case ast.MethodCall(name, arguments, _) =>
          if (Names.isAnnotation(name)) 0
          else maxDepth(arguments)
        case _: ast.NewStmt => 0
        case ast.LocalVarAssign(_, value) =>
          depth(value)
        case ast.FieldAssign(target, value) =>
          maxDepth(Seq(target, value))
        case _: ast.Literal => 0
        case _: ast.LocalVar => 0
        case ast.FieldAccess(receiver, _) =>
          depth(receiver) + 1
        case ast.UnExp(argument) =>
          depth(argument)
        case ast.BinExp(left, right) =>
          maxDepth(Seq(left, right))
        case _ => ???
      }

    /**
      * Computes the maximal unfold depth among the given nodes.
      *
      * @param nodes The nodes.
      * @return The maximal unfold depth.
      */
    def maxDepth(nodes: Seq[ast.Node]): Int =
      nodes
        .map { node => depth(node) }
        .reduceOption { (left, right) => math.max(left, right) }
        .getOrElse(0)

    maxDepth(statements)
  }

  /**
    * The depth upt to which specifications should be folded (equal to the unfold depth but accounting for the fold
    * delta if heuristics are enabled).
    */
  lazy val foldDepth: Int =
    if (Settings.useAnnotations) unfoldDepth
    else unfoldDepth + Settings.foldDelta
}

/**
  * Helper object used to extract annotations from info fields in the ast.
  */
object Annotations {
  def extract(infoed: ast.Infoed): Seq[Annotation] =
    if (Settings.useAnnotations) infoed
      .info
      .getUniqueInfo[AnnotationInfo]
      .map { info => info.annotations }
      .getOrElse(Seq.empty)
    else Seq.empty
}

/**
  * An annotation.
  *
  * @param name      The name.
  * @param arguments The argument.
  */
case class Annotation(name: String, argument: ast.Exp) {
  override def toString: String = s"$name($argument)"
}

/**
  * An info holding a sequence of annotations.
  *
  * @param annotations The annotations.
  */
case class AnnotationInfo(annotations: Seq[Annotation]) extends ast.Info {
  override def comment: Seq[String] = Seq.empty

  override def isCached: Boolean = false
}

/**
  * Utility object used providing a method to collect checks form aa program.
  */
object Checks {

  import rpi.util.Expressions._
  import rpi.util.Statements._

  /**
    * Collects checks from the given program.
    * @param program The program.
    *
    * @return The checks.
    */
  def collect(program: ast.Program): Seq[Check] = {
    // build map used to look up methods
    val methods: Map[String, ast.Method] = program
      .methods
      .map { method => method.name -> method }
      .toMap

    // variable used to accumulate checks
    var checks: Seq[Check] = Seq.empty

    def processSequence(sequence: ast.Seqn): ast.Seqn = {
      val processedStatements = processStatements(Seq.empty, sequence.ss)
      makeSequence(processedStatements)
    }

    @tailrec
    def processStatements(past: Seq[ast.Stmt], current: Seq[ast.Stmt]): Seq[ast.Stmt] = {
      current match {
        case statement +: future =>
          val (newPast, newCurrent) = statement match {
            // process sequence
            case ast.Seqn(statements, _) =>
              // flatten
              (past, statements ++ future)
            // process conditional
            case ast.If(condition, thenBody, elseBody) =>
              // process branches
              val processedThen = processSequence(thenBody)
              val processedElse = processSequence(elseBody)
              val processedConditional = ast.If(condition, processedThen, processedElse)()
              // advance
              (past :+ processedConditional, future)
            // process loop
            case ast.While(condition, invariants, body) =>
              // add check for loop body
              addCheck(invariants :+ condition, invariants, body)
              // trim annotations (ignored if disabled)
              val (pastAnnotations, trimmedPast) = trimAnnotationSuffix(past)
              val (futureAnnotations, trimmedFuture) = trimAnnotationPrefix(future)
              val exhaleInfo = AnnotationInfo(pastAnnotations)
              val inhaleInfo = AnnotationInfo(futureAnnotations)
              // compute exhales and inhales corresponding to loop specification
              val exhales = invariants.map { expression => ast.Exhale(expression)(info = exhaleInfo) }
              val inhales = invariants.map { expression => ast.Inhale(expression)(info = inhaleInfo) } :+ ast.Inhale(makeNot(condition))()
              // havoc variables
              val havoc = {
                val assignments = body
                  .writtenVars
                  .map { variable => ast.LocalVarAssign(variable, variable)() }
                ast.While(ast.FalseLit()(), Seq.empty, makeSequence(assignments))()
              }
              // advance
              (trimmedPast ++ exhales ++ Seq(havoc) ++ inhales, trimmedFuture)
            // process method call
            case ast.MethodCall(name, arguments, _) if !Names.isAnnotation(name) =>
              // extract annotations before and after
              val (pastAnnotations, trimmedPast) = trimAnnotationSuffix(past)
              val (futureAnnotations, trimmedFuture) = trimAnnotationPrefix(future)
              val exhaleInfo = AnnotationInfo(pastAnnotations)
              val inhaleInfo = AnnotationInfo(futureAnnotations)
              // compute exhales and inhales corresponding to method specification
              val method = methods(name)
              val bindings = substitutionMap(method.formalArgs, arguments)
              val exhales = method.pres.map { expression => ast.Exhale(substitute(expression, bindings))(info = exhaleInfo) }
              val inhales = method.posts.map { expression => ast.Inhale(substitute(expression, bindings))(info = inhaleInfo) }
              // advance
              (trimmedPast ++ exhales ++ inhales, trimmedFuture)
            // process any other statement
            case _ =>
              // advance
              (past :+ statement, future)
          }
          // recursively process advanced state
          processStatements(newPast, newCurrent)
        case _ => past
      }
    }

    def addCheck(preconditions: Seq[ast.Exp], postconditions: Seq[ast.Exp], body: ast.Seqn): Unit = {
      // trim annotations (ignored if disabled)
      val (prefixAnnotations, withoutPrefix) = trimAnnotationPrefix(body.ss)
      val (suffixAnnotations, trimmed) = trimAnnotationSuffix(withoutPrefix)
      val inhaleInfo = AnnotationInfo(prefixAnnotations)
      val exhaleInfo = AnnotationInfo(suffixAnnotations)
      // compute inhale and exhales corresponding to loop specification
      val inhales = preconditions.map { expression => ast.Inhale(expression)(info = inhaleInfo) }
      val exhales = postconditions.map { expression => ast.Exhale(expression)(info = exhaleInfo) }
      // process loop body
      val processedBody = processStatements(Seq.empty, trimmed)
      // create and add check
      val check = Check(inhales ++ processedBody ++ exhales)
      checks = checks :+ check
    }

    //
    program
      .methods
      .foreach {
        case ast.Method(_, _, _, preconditions, postconditions, Some(body)) =>
          addCheck(preconditions, postconditions, body)
        case _ => // do nothing
      }

    // return checks
    checks
  }

  private def trimAnnotationSuffix(statements: Seq[ast.Stmt]): (Seq[Annotation], Seq[ast.Stmt]) =
    statements match {
      case rest :+ ast.MethodCall(name, Seq(argument), _) if Names.isAnnotation(name) =>
        if (Settings.useAnnotations) {
          val (suffix, trimmed) = trimAnnotationSuffix(rest)
          val annotation = Annotation(name, argument)
          (suffix :+ annotation, trimmed)
        } else trimAnnotationSuffix(rest)
      case _ => (Seq.empty, statements)
    }

  private def trimAnnotationPrefix(statements: Seq[ast.Stmt]): (Seq[Annotation], Seq[ast.Stmt]) =
    statements match {
      case ast.MethodCall(name, Seq(argument), _) +: rest if Names.isAnnotation(name) =>
        if (Settings.useAnnotations) {
          val (prefix, trimmed) = trimAnnotationPrefix(rest)
          val annotation = Annotation(name, argument)
          (annotation +: prefix, trimmed)
        } else trimAnnotationPrefix(rest)
      case _ => (Seq.empty, statements)
    }
}