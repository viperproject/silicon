package rpi.teacher

import rpi.{Settings, Names}
import rpi.inference._
import viper.silver.ast
import viper.silver.verifier.{Failure, Success, VerificationError}

/**
  * The teacher providing the examples.
  *
  * @param inference The pointer to the inference.
  */
class Teacher(val inference: Inference) {
  /**
    * The builder used to build the programs used to check hypotheses.
    */
  private val builder = new CheckBuilder(teacher = this)

  /**
    * The extractor used to extract examples from verification errors.
    */
  private val extractor = new ExampleExtractor(teacher = this)

  /**
    * The list of all checks.
    */
  private val checks: Seq[Seq[ast.Seqn]] = {
    val collected = Checks.collect(inference.labeled)
    if (Settings.batch) Seq(collected)
    else collected.map { check => Seq(check) }
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
  def check(hypothesis: Hypothesis): Seq[Example] = {
    // self-framing check
    val framing = {
      val (check, context) = builder.framingCheck(hypothesis)
      execute(check, error => extractor.extractFraming(error, context))
    }
    // other checks, if hypothesis is self-framing
    if (framing.isEmpty)
      checks
        .flatMap { group =>
          val (check, context) = builder.basicCheck(group, hypothesis)
          execute(check, error => extractor.extractBasic(error, context))
        }
    else framing
  }

  /**
    * Executes the check represented by the given program and uses the given extraction method to produce examples in
    * case there are failures.
    *
    * @param program The check program.
    * @param extract The method extracting examples from verification errors.
    * @return The extracted examples.
    */
  private def execute(program: ast.Program, extract: VerificationError => Example): Seq[Example] =
    inference.verify(program) match {
      case Success => Seq.empty
      case Failure(errors) => errors
        .map {
          case error: VerificationError => extract(error)
          case _ => ??? // TODO: Error handling.
        }
    }
}

/**
  * A context object used to pass information from the check builder to the example extractor.
  */
class Context {
  /**
    * The labels and instances of the inhaled and exhaled states.
    */
  private var snapshots: Seq[(String, Instance)] = Seq.empty

  /**
    * A map holding variable names for all states.
    */
  private var names: Map[String, Map[ast.LocationAccess, String]] = Map.empty

  /**
    * Returns the labels and instances of all inhaled and exhaled states. Since the labels were added in topological
    * order with respect to the control flow, the labels are guaranteed to appear in that order in any actual execution,
    * if they are encountered (note: there are no loops as they are handled modularly).
    *
    * @return The labels of all inhaled and exhale states.
    */
  def allSnapshots: Seq[(String, Instance)] =
    snapshots

  /**
    * Adds the given instance as an instance corresponding to an inhaled state.
    *
    * @param label    The label of the state.
    * @param instance The instance.
    */
  def addSnapshot(label: String, instance: Instance): Unit = {
    snapshots = snapshots :+ (label, instance)
  }

  /**
    * Returns the name of the variable associated with the given location access in the given state.
    *
    * @param label  The label of the state.
    * @param access The location access.
    * @return The variable name.
    */
  def getName(label: String, access: ast.LocationAccess): String = {
    names(label)(access)
  }

  /**
    * Associates the given location access with the given variable name in the state with the given label.
    *
    * @param label  The label of the state.
    * @param access The location access.
    * @param name   The variable name.
    */
  def addName(label: String, access: ast.LocationAccess, name: String): Unit = {
    val updated = names
      .getOrElse(label, Map.empty)
      .updated(access, name)
    names = names.updated(label, updated)
  }
}

trait ContextInfo extends ast.Info {
  override def isCached: Boolean = false
}

case class FramingInfo(location: ast.LocationAccess) extends ContextInfo {
  override def comment: Seq[String] =
    Seq.empty
}

case class BasicInfo(label: String, instance: Instance) extends ContextInfo {
  override def comment: Seq[String] =
    Seq(instance.name)
}

/**
  * Utility object providing methods to collect checks from programs.
  */
object Checks {
  // import utility methods

  import rpi.util.Expressions._
  import rpi.util.Statements._

  /**
    * Collects and returns the checks corresponding to the given program.
    *
    * @param program The program.
    * @return The collected checks.
    */
  def collect(program: ast.Program): Seq[ast.Seqn] = {
    // build map used to look up methods
    implicit val methods: Map[String, ast.Method] = program
      .methods
      .map { method => method.name -> method }
      .toMap

    // collect checks from all methods
    program
      .methods
      .flatMap {
        case ast.Method(_, _, _, preconditions, postconditions, Some(body)) =>
          val inhales = preconditions.map { expression => ast.Inhale(expression)() }
          val exhales = postconditions.map { expression => ast.Exhale(expression)() }
          // collect checks
          if (Settings.useFraming) {
            val (updated, collected) = collectFramed(inhales, body)
            val check = asSequence(updated ++ exhales)
            check +: collected
          } else {
            val prefixes = Seq(inhales)
            val (updated, collected) = collectUnframed(prefixes, body)
            val checks = updated.map { prefix => asSequence(prefix ++ exhales) }
            collected ++ checks
          }
        case _ => Seq.empty
      }
  }

  private def collectFramed(prefix: Seq[ast.Stmt], statement: ast.Stmt)
                           (implicit methods: Map[String, ast.Method]): (Seq[ast.Stmt], Seq[ast.Seqn]) =
    statement match {
      // process sequence
      case ast.Seqn(statements, _) =>
        val empty = Seq.empty[ast.Seqn]
        statements.foldLeft((prefix, empty)) {
          case ((currentPrefix, currentCollected), inner) =>
            // process inner statement
            val (updated, collected) = collectFramed(currentPrefix, inner)
            // return combined results
            val combined = currentCollected ++ collected
            (updated, combined)
        }
      // process conditional
      case ast.If(condition, thenBody, elseBody) =>
        // process branches
        val (thenUpdated, thenCollected) = collectFramed(Seq.empty, thenBody)
        val (elseUpdated, elseCollected) = collectFramed(Seq.empty, elseBody)
        // updated conditional
        val conditional = ast.If(condition, asSequence(elseUpdated), asSequence(thenUpdated))()
        // return combined results
        val updated = prefix :+ conditional
        val combined = thenCollected ++ elseCollected
        (updated, combined)
      // process loop
      case ast.While(condition, invariants, body) =>
        // get inhales and exhales specifying loop
        val inhales = invariants.map { expression => ast.Inhale(expression)() }
        val exhales = invariants.map { expression => ast.Exhale(expression)() }
        // process loop body
        val collected = {
          val loopPrefix = inhales :+ ast.Inhale(condition)()
          val (loopUpdated, loopCollected) = collectFramed(loopPrefix, body)
          val check = asSequence(loopUpdated ++ exhales)
          loopCollected :+ check
        }
        // havoc variables
        val havocLoop = {
          val assignments = body
            .writtenVars
            .map { variable => ast.LocalVarAssign(variable, variable)() }
          ast.While(ast.FalseLit()(), Seq.empty, asSequence(assignments))()
        }
        // update prefix
        val updated = prefix ++ exhales ++ Seq(havocLoop) ++ inhales ++ Seq(ast.Inhale(not(condition))())
        // return result
        (updated, collected)
      // process method call
      case ast.MethodCall(name, arguments, _) if !Names.isAnnotation(name) =>
        // get inhales and exhales specifying method
        val method = methods(name)
        val map = computeMap(method.formalArgs, arguments)
        val exhales = method.pres.map { expression => ast.Exhale(substitute(expression, map))() }
        val inhales = method.posts.map { expression => ast.Inhale(substitute(expression, map))() }
        // return result
        val updated = prefix ++ exhales ++ inhales
        (updated, Seq.empty)
      // process any other statement
      case _ =>
        val updated = prefix :+ statement
        (updated, Seq.empty)
    }

  private def collectUnframed(prefixes: Seq[Seq[ast.Stmt]], statement: ast.Stmt)
                             (implicit methods: Map[String, ast.Method]): (Seq[Seq[ast.Stmt]], Seq[ast.Seqn]) = {
    // check whether the statement is complex, i.e., contains a loop or method call
    val isComplex = statement.exists {
      case _: ast.While => true
      case _: ast.MethodCall => true
      case _ => false
    }
    // process statement
    if (isComplex) collectComplex(prefixes, statement)
    else {
      val updated = prefixes.map { prefix => prefix :+ statement }
      (updated, Seq.empty)
    }
  }

  private def collectComplex(prefixes: Seq[Seq[ast.Stmt]], statement: ast.Stmt)
                            (implicit methods: Map[String, ast.Method]): (Seq[Seq[ast.Stmt]], Seq[ast.Seqn]) =
    statement match {
      // process sequence
      case ast.Seqn(statements, _) =>
        val empty = Seq.empty[ast.Seqn]
        statements.foldLeft((prefixes, empty)) {
          case ((currentPrefixes, checks), inner) =>
            // process inner statement
            val (updated, collected) = collectComplex(currentPrefixes, inner)
            // return combined results
            val combined = checks ++ collected
            (updated, combined)
        }
      // process conditional
      case ast.If(condition, thenBody, elseBody) =>
        // process branches
        val thenPrefixes = prefixes.map { prefix => prefix :+ ast.Inhale(condition)() }
        val elsePrefixes = prefixes.map { prefix => prefix :+ ast.Inhale(not(condition))() }
        val (thenUpdated, thenCollected) = collectUnframed(thenPrefixes, thenBody)
        val (elseUpdated, elseCollected) = collectUnframed(elsePrefixes, elseBody)
        // return combined results
        val updated = thenUpdated ++ elseUpdated
        val combined = thenCollected ++ elseCollected
        (updated, combined)
      // process loop
      case ast.While(condition, invariants, body) =>
        // prepare prefixes (inside loop and after loop)
        val inhales = invariants.map { expression => ast.Inhale(expression)() }
        val exhales = invariants.map { expression => ast.Exhale(expression)() }
        val inner = Seq(inhales :+ ast.Inhale(condition)())
        val after = Seq(inhales :+ ast.Inhale(not(condition))())
        // process loop body
        val (updated, collected) = collectUnframed(inner, body)
        // create checks (before loop and last inside loop)
        val before = prefixes.map { prefix => asSequence(prefix ++ exhales) }
        val last = updated.map { prefix => asSequence(prefix ++ exhales) }
        // return combined result
        val combined = before ++ collected ++ last
        (after, combined)
      // process method call
      case ast.MethodCall(name, arguments, _) if !Names.isAnnotation(name) =>
        // get inhales and exhales specifying method
        val method = methods(name)
        val map = computeMap(method.formalArgs, arguments)
        val exhales = method.pres.map { expression => ast.Exhale(substitute(expression, map))() }
        val inhales = method.posts.map { expression => ast.Inhale(substitute(expression, map))() }
        // checks before and prefixes after
        val before = prefixes.map { prefix => asSequence(prefix ++ exhales) }
        val after = Seq(inhales)
        // return result
        (after, before)
      // process any other statement
      case _ =>
        val updated = prefixes.map { prefix => prefix :+ statement }
        (updated, Seq.empty)
    }
}