package rpi.teacher

import rpi.{Names, Settings}
import viper.silver.ast

import scala.annotation.tailrec

case class Check(statements: Seq[ast.Stmt])

case class AnnotationInfo(name: String, arguments: Seq[ast.Exp]) extends ast.Info {
  override def comment: Seq[String] = Seq(s"$name(${arguments.mkString(", ")})")

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
      asSequence(processedStatements)
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
              // extract annotations before and after
              val (exhaleInfo, updatedPast) = annotationSuffix(past)
              val (inhaleInfo, updatedFuture) = annotationPrefix(future)
              // compute exhales and inhales corresponding to loop specification
              val exhales = invariants.map { expression => ast.Exhale(expression)(info = exhaleInfo) }
              val inhales = invariants.map { expression => ast.Inhale(expression)(info = inhaleInfo) } :+ ast.Inhale(not(condition))()
              // havoc variables
              val havoc = {
                val assignments = body
                  .writtenVars
                  .map { variable => ast.LocalVarAssign(variable, variable)() }
                ast.While(ast.FalseLit()(), Seq.empty, asSequence(assignments))()
              }
              // advance
              (updatedPast ++ exhales ++ Seq(havoc) ++ inhales, updatedFuture)
            // process method call
            case ast.MethodCall(name, arguments, _) if !Names.isAnnotation(name) =>
              // extract annotations before and after
              val (exhaleInfo, updatedPast) = annotationSuffix(past)
              val (inhaleInfo, updatedFuture) = annotationPrefix(future)
              // compute exhales and inhales corresponding to method specification
              val method = methods(name)
              val bindings = substitutionMap(method.formalArgs, arguments)
              val exhales = method.pres.map { expression => ast.Exhale(substitute(expression, bindings))(info = exhaleInfo) }
              val inhales = method.posts.map { expression => ast.Inhale(substitute(expression, bindings))(info = inhaleInfo) }
              // advance
              (updatedPast ++ exhales ++ inhales, updatedFuture)
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
      // extract annotations in the beginning and at the end
      val (inhaleInfo, withoutPrefix) = annotationPrefix(body.ss)
      val (exhaleInfo, withoutSuffix) = annotationSuffix(withoutPrefix)
      // compute inhale and exhales corresponding to loop specification
      val inhales = preconditions.map { expression => ast.Inhale(expression)(info = inhaleInfo) }
      val exhales = postconditions.map { expression => ast.Exhale(expression)(info = exhaleInfo) }
      // process loop body
      val processedBody = processStatements(Seq.empty, withoutSuffix)
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

  private def annotationSuffix(past: Seq[ast.Stmt]): (ast.Info, Seq[ast.Stmt]) =
    past match {
      case rest :+ ast.MethodCall(name, arguments, _) if Names.isAnnotation(name) =>
        val info = if (Settings.useAnnotations) AnnotationInfo(name, arguments) else ast.NoInfo
        val (infos, remaining) = annotationSuffix(rest)
        (ast.MakeInfoPair(infos, info), remaining)
      case _ => (ast.NoInfo, past)
    }

  private def annotationPrefix(future: Seq[ast.Stmt]): (ast.Info, Seq[ast.Stmt]) =
    future match {
      case ast.MethodCall(name, arguments, _) +: rest if Names.isAnnotation(name) =>
        val info = if (Settings.useAnnotations) AnnotationInfo(name, arguments) else ast.NoInfo
        val (infos, remaining) = annotationPrefix(rest)
        (ast.MakeInfoPair(info, infos), remaining)
      case _ => (ast.NoInfo, future)
    }
}
