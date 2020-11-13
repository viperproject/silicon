package rpi.teacher

import rpi._
import viper.silicon.Silicon
import viper.silver.{ast => sil}
import viper.silver.verifier._

class Teacher(val inference: Inference) {
  /**
    * The instance of the silicon verifier used to generate examples.
    */
  private val verifier: Verifier = {
    // create instance
    val instance = new Silicon()
    // pass arguments
    val args = Seq(
      "--z3Exe", Inference.z3,
      "--counterexample", "raw",
      "--ignoreFile", "dummy.vpr")
    instance.parseCommandLine(args)
    // return instance
    instance
  }

  private val builder: ProgramBuilder = new ProgramBuilder(this)

  /**
    * The example extractor used to extract examples from verification errors.
    */
  private val extractor = new ExampleExtractor(teacher = this)

  /**
    * Starts the teacher and all of its subcomponents.
    */
  def start(): Unit = {
    verifier.start()
  }

  /**
    * Stops the teacher and all of its subcomponents.
    */
  def stop(): Unit = {
    verifier.stop()
  }

  /**
    * Checks whether the given hypothesis is valid and returns a non-empty sequence counter examples if it is not.
    *
    * @param hypothesis The hypothesis to check.
    * @return The sequence of counter examples.
    */
  def check(hypothesis: Seq[sil.Predicate]): Seq[Example] = inference
    .triples.flatMap { triple =>
    // build program
    val program = builder.buildCheck(triple, hypothesis)
    println(program)
    // verify program and extract examples
    verify(program) match {
      case Success => Seq.empty
      case Failure(errors) => errors
        .collect { case error: VerificationError => error }
        .map { error =>
          val pre = getInstance(triple.pres)
          val post = getInstance(triple.posts)
          extractor.extract(error, pre, post)
        }
    }
  }

  def getInstance(expressions: Seq[sil.Exp]): Instance =
    expressions
      .collectFirst { case predicate: sil.PredicateAccessPredicate =>
        val access = predicate.loc
        val name = access.predicateName
        val specification = inference.specifications(name)
        val arguments = access.args
        Instance(specification, arguments)
      }.get

  /**
    * Verifies the given program.
    *
    * @param program The program to verify.
    * @return The verification result.
    */
  def verify(program: sil.Program): VerificationResult = verifier.verify(program)

  def encode(expression: sil.Exp): String = expression match {
    case sil.LocalVar(name, _) => name
    case sil.FieldAccess(receiver, sil.Field(name, _)) => s"${encode(receiver)}_$name"
    case sil.PredicateAccess(arguments, name) => s"${name}___${arguments.map(encode).mkString("_")}___"
  }
}

/**
  * Labels used to label states.
  */
object Labels {
  val PRE_STATE = "pre"
  val CURRENT_STATE = "current"
  val POST_STATE = "post"
}
