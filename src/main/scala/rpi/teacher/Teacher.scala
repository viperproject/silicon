package rpi.teacher

import rpi.Configuration
import rpi.inference._
import viper.silver.ast
import viper.silver.verifier.{Failure, Success, VerificationError}

/**
  * The teacher providing the samples.
  *
  * @param context The pointer to the context.
  */
class Teacher(val context: Context) {
  /**
    * The builder used to build the programs used to check hypotheses.
    */
  private val builder = new CheckBuilder(teacher = this)

  /**
    * The list of all checks.
    */
  private val checks = {
    // read configuration
    val configuration = context.configuration
    val useAnnotations = configuration.useAnnotations()
    val noBatching = configuration.noBranching()
    // collect checks
    val collected = Checks.collect(context.labeled, useAnnotations)
    if (noBatching) collected.map { check => Seq(check) }
    else Seq(collected)
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
    * valid, a non-empty sequence of samples is returned.
    *
    * @param hypothesis The hypothesis to check.
    * @return The sequence of samples.
    */
  def check(hypothesis: Hypothesis): Seq[Sample] = {
    // self-framing check
    val framing = {
      val (check, context) = builder.framingChecks(hypothesis)
      execute(check, error => SampleExtractor.extractFraming(error, context))
    }
    // other checks, if hypothesis is self-framing
    if (framing.isEmpty) checks
      .flatMap { group =>
        val (check, context) = builder.basicChecks(group, hypothesis)
        execute(check, error => SampleExtractor.extractBasic(error, context))
      }
    else framing
  }

  /**
    * Executes the check represented by the given program and uses the given extraction method to produce samples in
    * case there are failures.
    *
    * @param program The check program.
    * @param extract The method extracting samples from verification errors.
    * @return The extracted samples.
    */
  private def execute(program: ast.Program, extract: VerificationError => Sample): Seq[Sample] =
    context.inference.verify(program) match {
      case Success => Seq.empty
      case Failure(errors) => errors
        .map {
          case error: VerificationError => extract(error)
          case _ => ??? // TODO: Error handling.
        }
    }
}

/**
  * A context object used to pass information from the check builder to the sample extractor.
  */
class CheckContext(val configuration: Configuration) {
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

trait CheckInfo extends ast.Info {
  override def isCached: Boolean = false
}

case class FramingInfo(location: ast.LocationAccess) extends CheckInfo {
  override def comment: Seq[String] =
    Seq.empty
}

case class BasicInfo(label: String, instance: Instance) extends CheckInfo {
  override def comment: Seq[String] =
    Seq(instance.toString)
}
