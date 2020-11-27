package rpi.teacher

import rpi.{Config, Names}
import rpi.inference._
import rpi.util.Expressions
import viper.silver.verifier.{Failure, Success, VerificationError}
import viper.silver.{ast => sil}

/**
  * The teacher providing the examples.
  *
  * @param inference The pointer to the inference.
  */
class Teacher(val inference: Inference) {

  private val builder = new CheckBuilder(teacher = this)

  private val extractor = new ExampleExtractor(teacher = this)

  /**
    * The list of all checks.
    */
  private val checks: Seq[Check] = {
    val program = inference.labeled
    val methods = program
      .methods
      .map { method => method.name -> method }
      .toMap

    // helper method to collect checks
    def collect(prefixes: Seq[Seq[sil.Stmt]], statement: sil.Stmt): (Seq[Seq[sil.Stmt]], Seq[Check]) = {
      // check whether statement is complex, i.e., contains a loop or method call
      val isComplex = statement.exists {
        case _: sil.While => true
        case _: sil.MethodCall => true
        case _ => false
      }
      // actual check collecting
      if (isComplex) complexCollect(prefixes, statement)
      else {
        val updated = prefixes.map { prefix => prefix :+ statement }
        (updated, Seq.empty)
      }
    }

    // other helper method to collect checks
    def complexCollect(prefixes: Seq[Seq[sil.Stmt]], statement: sil.Stmt): (Seq[Seq[sil.Stmt]], Seq[Check]) =
      statement match {
        case sil.Seqn(statements, _) =>
          statements.foldLeft((prefixes, Seq.empty[Check])) {
            case ((currentPrefixes, checks), currentStatement) =>
              // process statement
              val (updated, collected) = complexCollect(currentPrefixes, currentStatement)
              // combine results
              val combined = checks ++ collected
              (updated, combined)
          }
        case sil.If(condition, thenBody, elseBody) =>
          if (Config.useFraming) ???
          else {
            // process branches
            val thenPrefixes = prefixes.map { prefix => prefix :+ sil.Inhale(condition)() }
            val elsePrefixes = prefixes.map { prefix => prefix :+ sil.Inhale(Expressions.negate(condition))() }
            val (thenUpdated, thenCollected) = collect(thenPrefixes, thenBody)
            val (elseUpdated, elseCollected) = collect(elsePrefixes, elseBody)
            // combine results
            val updated = thenUpdated ++ elseUpdated
            val combined = thenCollected ++ elseCollected
            (updated, combined)
          }
        case sil.While(condition, invariants, body) =>
          val inhales = invariants.map { invariant => sil.Inhale(invariant)() }
          val exhales = invariants.map { invariant => sil.Exhale(invariant)() }
          if (Config.useFraming) ???
          else {
            // prepare prefixes (inside loop and after loop)
            val inner = Seq(inhales :+ sil.Inhale(condition)())
            val after = Seq(inhales :+ sil.Inhale(Expressions.negate(condition))())
            // process loop body
            val (updated, collectedChecks) = collect(inner, body)
            // create checks (before the loop and last inside loop)
            val beforeChecks = prefixes.map { prefix => Check(prefix ++ exhales) }
            val lstChecks = updated.map { prefix => Check(prefix ++ exhales) }
            // combine results
            val combined = beforeChecks ++ collectedChecks ++ lstChecks
            (after, combined)
          }
        case sil.MethodCall(name, arguments, _) if !Names.isAnnotation(name) =>
          val method = methods(name)
          val map = Expressions.computeMap(method.formalArgs, arguments)
          val exhales = method.pres.map { condition => sil.Exhale(Expressions.substitute(condition, map))() }
          val inhales = method.posts.map { condition => sil.Inhale(Expressions.substitute(condition, map))() }
          if (Config.useFraming) ???
          else {
            val checks = prefixes.map { prefix => Check(prefix ++ exhales) }
            val after = Seq(inhales)
            (after, checks)
          }
        case _ =>
          val updated = prefixes.map { prefix => prefix :+ statement }
          (updated, Seq.empty)
      }

    // collect from all methods
    program
      .methods
      .flatMap {
        case sil.Method(_, _, _, pres, posts, Some(body)) =>
          val inhales = pres.map { condition => sil.Inhale(condition)() }
          val exhales = posts.map { condition => sil.Exhale(condition)() }
          // process method body
          val prefixes = Seq(inhales)
          val (updated, collected) = collect(prefixes, body)
          // create checks (last of method)
          val last = updated.map { prefix => Check(prefix ++ exhales) }
          // combine results
          collected ++ last
        case _ => Seq.empty
      }
  }

  /**
    * Starts the teacher and all of its subcomponents.
    */
  def start(): Unit = {
  }

  /**
    * Stops the teacher and all of its subcomponents.
    */
  def stop(): Unit = {
  }

  /**
    * Checks the given hypothesis. If the hypothesis is valid, an empty sequence is returned. If the hypothesis is not
    * valid, a non-empty sequence of examples is returned.
    *
    * @param hypothesis The hypothesis to check.
    * @return The sequence of examples.
    */
  def check(hypothesis: Hypothesis): Seq[Example] =
    checks.flatMap { check => basicCheck(check, hypothesis) }

  private def basicCheck(check: Check, hypothesis: Hypothesis): Seq[Example] = {
    // build program
    val (program, context) = builder.basicCheck(check, hypothesis)
    if (Config.debugPrintProgram) println(program)
    // extract example
    val result = inference.verify(program)
    result match {
      case Success => Seq.empty
      case Failure(errors) => errors
        .collect { case error: VerificationError => error }
        .map { error =>
          println(error)
          val example = extractor.extract(error, context)
          println(example)
          example
        }
    }
  }

  private def framingCheck(): Example = ???
}

case class Check(statements: Seq[sil.Stmt])

class Context() {
  private var instances: Map[String, Instance] = Map.empty
  private var variables: Map[sil.LocationAccess, String] = Map.empty

  def instance(label: String): Instance =
    instances(label)

  def variable(location: sil.LocationAccess): String =
    variables(location)

  def addInstance(label: String, instance: Instance): Unit =
    instances = instances.updated(label, instance)

  def addVariable(location: sil.LocationAccess, variable: String): Unit =
    variables = variables.updated(location, variable)
}