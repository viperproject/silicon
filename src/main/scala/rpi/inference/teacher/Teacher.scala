package rpi.inference.teacher

import rpi.Configuration
import rpi.inference.context.{Context, Instance}
import rpi.inference._
import rpi.inference.teacher.query.QueryBuilder
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
  private val builder = new QueryBuilder(context)

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
      // TODO: Only perform if syntactic structure suggests that framing might be an issue.
      val (check, context) = builder.framingQuery(hypothesis)
      execute(check, error => SampleExtractor.extractFraming(error, context))
    }
    // other checks, if hypothesis is self-framing
    if (framing.isEmpty)
      context
        .batches
        .flatMap { batch =>
          val (check, context) = builder.basicQuery(batch, hypothesis)
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
    context.verifier.verify(program) match {
      case Success => Seq.empty
      case Failure(errors) => errors
        .map {
          case error: VerificationError => extract(error)
          case error => sys.error(s"Unexpected verification failure: $error")
        }
    }
}

/**
  * A context object used to pass information from the query builder to the sample extractor.
  */
// TODO: No configuration here.
// TODO: Probably rework entirely.
class QueryContext(val configuration: Configuration) {
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
