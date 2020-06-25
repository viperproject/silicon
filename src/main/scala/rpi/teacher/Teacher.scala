package rpi.teacher

import rpi.{Inference, Sample}
import viper.silicon.Silicon
import viper.silver.ast._
import viper.silver.verifier._

/**
  * The teacher providing the learner with positive, negative, and implication samples.
  */
class Teacher(program: Program) {
  /**
    * The instance of the silicon verifier used to generate the samples.
    */
  private lazy val verifier: Verifier = {
    // create instance
    val instance = new Silicon()
    // pass arguments
    val arguments = Seq(
      "--z3Exe", Inference.z3,
      "--counterexample", "native",
      "--ignoreFile", "dummy.vpr")
    instance.parseCommandLine(arguments)
    // return instance
    instance
  }

  /**
    * For now, we assume that there is only one loop. At some point, we will lift this restriction.
    */
  private lazy val loop: Loop = {
    val loops = program.methods.flatMap(collectLoops)
    assert(loops.size == 1)
    loops.head
  }


  def check(hypothesis: Exp): Seq[Sample] = {
    val context = loop.context

    // build program
    val builder = new ProgramBuilder(context)
    builder.initialize()
    builder.inhale(hypothesis)
    builder.execute(loop.loop.body)
    builder.exhale(hypothesis)
    val program = builder.buildProgram()

    println(program)

    // verify program
    verifier.start()
    val result = verifier.verify(program)
    verifier.stop()

    result match {
      case Success => Seq.empty
      case Failure(errors) => errors
        .collect { case error: VerificationError => error }
        .flatMap { error => SampleExtractor.extract(error, context) }
    }
  }

  private def collectLoops(method: Method): Seq[Loop] = {
    // helper method
    def collect(node: Node): Seq[Loop] = node match {
      case Seqn(statements, declarations) => statements
        .flatMap(collect)
        .map(_.addDeclarations(declarations))
      case loop: While => Seq(Loop(loop, Context(program, method, Seq.empty)))
      case _ => Seq.empty
    }

    // collect loops contained in body of method
    method.body match {
      case Some(body) => collect(body)
      case None => Seq.empty
    }
  }
}

case class Loop(loop: While, context: Context) {
  def addDeclarations(declarations: Seq[Declaration]): Loop = copy(context = context.addDeclarations(declarations))
}

case class Context(program: Program, method: Method, declarations: Seq[Declaration]) {
  lazy val variables = declarations
    .collect { case declaration: LocalVarDecl => declaration }
    .map { declaration => LocalVar(declaration.name, declaration.typ)() }

  lazy val initials = variables
    .map { variable => LocalVar(s"${variable.name}_0", variable.typ)() -> variable }
    .toMap

  def addDeclarations(declarations: Seq[Declaration]): Context = copy(declarations = this.declarations ++ declarations)
}
