package rpi.teacher

import rpi.inference.{Hypothesis, Instance, InstanceInfo}
import rpi.util.ValueInfo
import rpi.Names
import viper.silver.ast

import scala.annotation.tailrec

case class Check(statements: Seq[ast.Stmt]) {
  /**
    * The instances corresponding to exhaled specifications appearing in the statements.
    */
  private val exhaled: Seq[Instance] =
    statements
      .flatMap {
        case ast.Exhale(predicate: ast.PredicateAccessPredicate) =>
          predicate.info.getUniqueInfo[InstanceInfo].map { info => info.instance }
        case _ => None
      }
      .distinct

  /**
    * The depth up to which specifications should be unfolded.
    *
    * Note: Ths is a very crude approximation.
    */
  private val statementsDepth: Int = maxDepth(statements)

  def baseDepth(hypothesis: Hypothesis): Int = {
    val specifications = exhaled.map { instance => hypothesis.getPredicateBody(instance) }
    val specificationDepth = maxDepth(specifications)
    math.max(statementsDepth, specificationDepth)
  }

  /**
    * Computes the unfold depth for the given node.
    *
    * @param node The node.
    * @return The unfold depth.
    */
  private def depth(node: ast.Node): Int =
    node match {
      // statements
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
      // expressions
      case _: ast.Literal => 0
      case _: ast.LocalVar => 0
      case ast.FieldAccess(receiver, _) =>
        depth(receiver) + 1
      case ast.UnExp(argument) =>
        depth(argument)
      case ast.BinExp(left, right) =>
        maxDepth(Seq(left, right))
      // resources
      case ast.FieldAccessPredicate(resource, _) =>
        depth(resource)
      case ast.PredicateAccessPredicate(resource, _) =>
        maxDepth(resource.args)
      case _ => ???
    }

  /**
    * Computes the maximal unfold depth among the given nodes.
    *
    * @param nodes The nodes.
    * @return The maximal unfold depth.
    */
  private def maxDepth(nodes: Seq[ast.Node]): Int =
    nodes
      .map { node => depth(node) }
      .reduceOption { (left, right) => math.max(left, right) }
      .getOrElse(0)

}

/**
  * Helper object used to extract annotations from info fields in the ast.
  */
object Annotations {
  def extract(node: ast.Infoed): Seq[Annotation] =
    node
      .info
      .getUniqueInfo[AnnotationInfo]
      .map { info => info.annotations }
      .getOrElse(Seq.empty)
}

/**
  * An annotation.
  *
  * @param name     The name.
  * @param argument The argument.
  */
case class Annotation(name: String, argument: ast.Exp) {
  override def toString: String = s"$name($argument)"
}

/**
  * An info holding a sequence of annotations.
  *
  * @param annotations The annotations.
  */
case class AnnotationInfo(annotations: Seq[Annotation]) extends ValueInfo

/**
  * Utility object used providing a method to collect checks form aa program.
  */
object Checks {

  import rpi.util.Expressions._
  import rpi.util.Statements._

  /**
    * Collects checks from the given program.
    *
    * @param program        The program.
    * @param useAnnotations The flag indicating whether annotations are enabled.
    * @return The checks.
    */
  def collect(program: ast.Program, useAnnotations: Boolean): Seq[Check] = {
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
              val (pastAnnotations, trimmedPast) = trimAnnotations(past)
              val info = AnnotationInfo(pastAnnotations)
              // compute exhales and inhales corresponding to loop specification
              val exhales = invariants.map { expression => ast.Exhale(expression)(info = info) }
              val inhales = invariants.map { expression => ast.Inhale(expression)() } :+ ast.Inhale(makeNot(condition))()
              // havoc variables
              val havoc = {
                val assignments = body
                  .writtenVars
                  .map { variable => ast.LocalVarAssign(variable, variable)() }
                ast.While(ast.FalseLit()(), Seq.empty, makeSequence(assignments))()
              }
              // advance
              (trimmedPast ++ exhales ++ Seq(havoc) ++ inhales, future)
            // process method call
            case ast.MethodCall(name, arguments, _) if !Names.isAnnotation(name) =>
              // extract annotations
              val (pastAnnotations, trimmedPast) = trimAnnotations(past)
              val info = AnnotationInfo(pastAnnotations)
              // compute exhales and inhales corresponding to method specification
              val method = methods(name)
              val bindings = substitutionMap(method.formalArgs, arguments)
              val exhales = method.pres.map { expression => ast.Exhale(substitute(expression, bindings))(info = info) }
              val inhales = method.posts.map { expression => ast.Inhale(substitute(expression, bindings))() }
              // advance
              (trimmedPast ++ exhales ++ inhales, future)
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
      val (suffixAnnotations, trimmed) = trimAnnotations(body.ss)
      val info = AnnotationInfo(suffixAnnotations)
      // compute inhale and exhales corresponding to loop specification
      val inhales = preconditions.map { expression => ast.Inhale(expression)() }
      val exhales = postconditions.map { expression => ast.Exhale(expression)(info = info) }
      // process loop body
      val processedBody = processStatements(Seq.empty, trimmed)
      // create and add check
      val check = Check(inhales ++ processedBody ++ exhales)
      checks = checks :+ check
    }

    def trimAnnotations(statements: Seq[ast.Stmt]): (Seq[Annotation], Seq[ast.Stmt]) =
      statements match {
        case rest :+ ast.MethodCall(name, Seq(argument), _) if Names.isAnnotation(name) =>
          if (useAnnotations) {
            val (suffix, trimmed) = trimAnnotations(rest)
            val annotation = Annotation(name, argument)
            (suffix :+ annotation, trimmed)
          } else trimAnnotations(rest)
        case _ => (Seq.empty, statements)
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
}