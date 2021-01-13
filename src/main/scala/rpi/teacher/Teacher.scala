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
  private val checks = {
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
    if (framing.isEmpty) checks
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
