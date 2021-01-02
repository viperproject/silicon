package rpi.teacher

import rpi.{Settings, Names}
import rpi.inference._
import viper.silver.verifier.{Failure, Success, VerificationError}
import viper.silver.{ast => sil}

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
  private val checks: Seq[Seq[sil.Seqn]] = {
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
  private def execute(program: sil.Program, extract: VerificationError => Example): Seq[Example] =
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
    * A map holding the instances corresponding to the inhaled states.
    */
  private var inhaled: Map[String, Instance] = Map.empty

  /**
    * A map holding the instances corresponding to the exhaled states.
    */
  private var exhaled: Map[String, Instance] = Map.empty

  /**
    * A map holding variable names for all states.
    */
  private var names: Map[String, Map[sil.LocationAccess, String]] = Map.empty

  /**
    * Returns whether the given label corresponds to an inhaled state or not.
    *
    * @param label The label of the state.
    * @return True if the given label corresponds to an inhaled state.
    */
  def isInhaled(label: String): Boolean =
    inhaled.contains(label)

  /**
    * Adds the given instance as an instance corresponding to an inhaled state.
    *
    * @param label    The label of the state.
    * @param instance The instance.
    */
  def addInhaled(label: String, instance: Instance): Unit =
    inhaled = inhaled.updated(label, instance)

  /**
    * Adds the given instance as an instance corresponding to an exhaled state.
    *
    * @param label    The label of the state.
    * @param instance The instance.
    */
  def addExhaled(label: String, instance: Instance): Unit =
    exhaled = exhaled.updated(label, instance)

  /**
    * Associates the given location access with the given variable name in the state with the given label.
    *
    * @param label  The label of the state.
    * @param access The location access.
    * @param name   The variable name.
    */
  def addName(label: String, access: sil.LocationAccess, name: String): Unit = {
    val updated = names
      .getOrElse(label, Map.empty)
      .updated(access, name)
    names = names.updated(label, updated)
  }

  /**
    * Returns the instance corresponding to the inhaled state with the given label.
    *
    * @param label The label of the state.
    * @return The instances.
    */
  def getInhaled(label: String): Instance =
    inhaled(label)

  /**
    * Returns the instance corresponding to the exhaled state with the given label.
    *
    * @param label The label of the state.
    * @return The instance.
    */
  def getExhaled(label: String): Instance =
    exhaled(label)

  /**
    * Returns the name of the variable associated with the given location access in the given state.
    *
    * @param label  The label of the state.
    * @param access The location access.
    * @return The variable name.
    */
  def getName(label: String, access: sil.LocationAccess): String = {
    names(label)(access)
  }
}

trait ContextInfo extends sil.Info {
  override def comment: Seq[String] = Seq.empty

  override def isCached: Boolean = false
}

case class FramingInfo(location: sil.LocationAccess) extends ContextInfo

case class BasicInfo(label: String, instance: Instance) extends ContextInfo

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
  def collect(program: sil.Program): Seq[sil.Seqn] = {
    // build map used to look up methods
    implicit val methods: Map[String, sil.Method] = program
      .methods
      .map { method => method.name -> method }
      .toMap

    // collect checks from all methods
    program
      .methods
      .flatMap {
        case sil.Method(_, _, _, preconditions, postconditions, Some(body)) =>
          val inhales = preconditions.map { expression => sil.Inhale(expression)() }
          val exhales = postconditions.map { expression => sil.Exhale(expression)() }
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

  private def collectFramed(prefix: Seq[sil.Stmt], statement: sil.Stmt)
                           (implicit methods: Map[String, sil.Method]): (Seq[sil.Stmt], Seq[sil.Seqn]) =
    statement match {
      // process sequence
      case sil.Seqn(statements, _) =>
        val empty = Seq.empty[sil.Seqn]
        statements.foldLeft((prefix, empty)) {
          case ((currentPrefix, currentCollected), inner) =>
            // process inner statement
            val (updated, collected) = collectFramed(currentPrefix, inner)
            // return combined results
            val combined = currentCollected ++ collected
            (updated, combined)
        }
      // process conditional
      case sil.If(condition, thenBody, elseBody) =>
        // process branches
        val (thenUpdated, thenCollected) = collectFramed(Seq.empty, thenBody)
        val (elseUpdated, elseCollected) = collectFramed(Seq.empty, elseBody)
        // updated conditional
        val conditional = sil.If(condition, asSequence(elseUpdated), asSequence(thenUpdated))()
        // return combined results
        val updated = prefix :+ conditional
        val combined = thenCollected ++ elseCollected
        (updated, combined)
      // process loop
      case sil.While(condition, invariants, body) =>
        // get inhales and exhales specifying loop
        val inhales = invariants.map { expression => sil.Inhale(expression)() }
        val exhales = invariants.map { expression => sil.Exhale(expression)() }
        // process loop body
        val collected = {
          val loopPrefix = inhales :+ sil.Inhale(condition)()
          val (loopUpdated, loopCollected) = collectFramed(loopPrefix, body)
          val check = asSequence(loopUpdated ++ exhales)
          loopCollected :+ check
        }
        // havoc variables
        val havocLoop = {
          val assignments = body
            .writtenVars
            .map { variable => sil.LocalVarAssign(variable, variable)() }
          sil.While(sil.FalseLit()(), Seq.empty, asSequence(assignments))()
        }
        // update prefix
        val updated = prefix ++ exhales ++ Seq(havocLoop) ++ inhales ++ Seq(sil.Inhale(not(condition))())
        // return result
        (updated, collected)
      // process method call
      case sil.MethodCall(name, arguments, _) if !Names.isAnnotation(name) =>
        // get inhales and exhales specifying method
        val method = methods(name)
        val map = computeMap(method.formalArgs, arguments)
        val exhales = method.pres.map { expression => sil.Exhale(substitute(expression, map))() }
        val inhales = method.posts.map { expression => sil.Inhale(substitute(expression, map))() }
        // return result
        val updated = prefix ++ exhales ++ inhales
        (updated, Seq.empty)
      // process any other statement
      case _ =>
        val updated = prefix :+ statement
        (updated, Seq.empty)
    }

  private def collectUnframed(prefixes: Seq[Seq[sil.Stmt]], statement: sil.Stmt)
                             (implicit methods: Map[String, sil.Method]): (Seq[Seq[sil.Stmt]], Seq[sil.Seqn]) = {
    // check whether the statement is complex, i.e., contains a loop or method call
    val isComplex = statement.exists {
      case _: sil.While => true
      case _: sil.MethodCall => true
      case _ => false
    }
    // process statement
    if (isComplex) collectComplex(prefixes, statement)
    else {
      val updated = prefixes.map { prefix => prefix :+ statement }
      (updated, Seq.empty)
    }
  }

  private def collectComplex(prefixes: Seq[Seq[sil.Stmt]], statement: sil.Stmt)
                            (implicit methods: Map[String, sil.Method]): (Seq[Seq[sil.Stmt]], Seq[sil.Seqn]) =
    statement match {
      // process sequence
      case sil.Seqn(statements, _) =>
        val empty = Seq.empty[sil.Seqn]
        statements.foldLeft((prefixes, empty)) {
          case ((currentPrefixes, checks), inner) =>
            // process inner statement
            val (updated, collected) = collectComplex(currentPrefixes, inner)
            // return combined results
            val combined = checks ++ collected
            (updated, combined)
        }
      // process conditional
      case sil.If(condition, thenBody, elseBody) =>
        // process branches
        val thenPrefixes = prefixes.map { prefix => prefix :+ sil.Inhale(condition)() }
        val elsePrefixes = prefixes.map { prefix => prefix :+ sil.Inhale(not(condition))() }
        val (thenUpdated, thenCollected) = collectUnframed(thenPrefixes, thenBody)
        val (elseUpdated, elseCollected) = collectUnframed(elsePrefixes, elseBody)
        // return combined results
        val updated = thenUpdated ++ elseUpdated
        val combined = thenCollected ++ elseCollected
        (updated, combined)
      // process loop
      case sil.While(condition, invariants, body) =>
        // prepare prefixes (inside loop and after loop)
        val inhales = invariants.map { expression => sil.Inhale(expression)() }
        val exhales = invariants.map { expression => sil.Exhale(expression)() }
        val inner = Seq(inhales :+ sil.Inhale(condition)())
        val after = Seq(inhales :+ sil.Inhale(not(condition))())
        // process loop body
        val (updated, collected) = collectUnframed(inner, body)
        // create checks (before loop and last inside loop)
        val before = prefixes.map { prefix => asSequence(prefix ++ exhales) }
        val last = updated.map { prefix => asSequence(prefix ++ exhales) }
        // return combined result
        val combined = before ++ collected ++ last
        (after, combined)
      // process method call
      case sil.MethodCall(name, arguments, _) if !Names.isAnnotation(name) =>
        // get inhales and exhales specifying method
        val method = methods(name)
        val map = computeMap(method.formalArgs, arguments)
        val exhales = method.pres.map { expression => sil.Exhale(substitute(expression, map))() }
        val inhales = method.posts.map { expression => sil.Inhale(substitute(expression, map))() }
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