package rpi.teacher

import rpi.{Inference, Sample}
import viper.silicon.Silicon
import viper.silver.ast._
import viper.silver.verifier._

object Teacher {
  val PRE_STATE_LABEL = "pre"
  val POST_STATE_LABEL = "post"
}

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
      "--counterexample", "raw",
      "--logLevel", "ALL",
      "--ignoreFile", "dummy.vpr")
    instance.parseCommandLine(arguments)
    // TODO: when do we stop the verifier?
    instance.start()
    // return instance
    instance
  }

  // COLLECT LOOPS --------------------

  /**
    * For now, we assume that there is only one loop. At some point, we will lift this restriction.
    */
  private lazy val loop: Loop = {
    val loops = program.methods.flatMap(collectLoops)
    assert(loops.size == 1)
    loops.head
  }

  private def collectLoops(method: Method): Seq[Loop] = {
    // helper method
    def collect(node: Node): Seq[Loop] = node match {
      case Seqn(stmts, decls) => stmts
        .flatMap(collect)
        .map(_.addDeclarations(decls))
      case loop: While => Seq(Loop(loop, Context(program, method, Seq.empty, atoms)))
      case _ => Seq.empty
    }

    // collect loops contained in body of method
    method.body match {
      case Some(body) => collect(body)
      case None => Seq.empty
    }
  }

  // COLLECT ATOMIC PREDICATES --------------

  private lazy val atoms: Seq[Exp] = program.methods.flatMap(collectAtomic)

  println(s"atomic predicates: $atoms")

  private def collectAtomic(method: Method): Seq[Exp] = {
    // TODO: Refine
    def collect(node: Node): Seq[Exp] = node match {
      case Seqn(stmts, _) => stmts.flatMap(collect).distinct
      case While(cond, _, body) => collect(body) :+ cond
      case _ => Seq.empty
    }

    method.body match {
      case Some(body) => collect(body)
      case None => Seq.empty
    }
  }

  def check(hypothesis: Exp): Seq[Sample] = {
    val context = loop.context

    // build program
    val builder = new ProgramBuilder(context)
    (context.vars() zip context.args()).foreach { case (v, a) =>
      val lhs = LocalVar(v.name, v.typ)()
      val rhs = LocalVar(a.name, a.typ)()
      builder.addStmt(LocalVarAssign(lhs, rhs)())
    }
    builder.addInhale(hypothesis)
    builder.addInhale(loop.loop.cond)
    atoms.zipWithIndex.foreach { case (exp, i) => builder.saveValue(atoms.head, s"p$i") }
    builder.addLabel(Teacher.PRE_STATE_LABEL)
    loop.stmts().foreach(builder.addStmt)
    builder.addLabel(Teacher.POST_STATE_LABEL)
    builder.addExhale(hypothesis)

    val program = builder.buildProgram()
    println(program)

    // verify program
    val result = verifier.verify(program)

    result match {
      case Success => Seq.empty
      case Failure(errors) => errors
        .collect { case error: VerificationError => error }
        .flatMap { error => SampleExtractor.extract(error, context) }
    }
  }

}

case class Loop(loop: While, context: Context) {
  def addDeclarations(declarations: Seq[Declaration]): Loop = copy(context = context.addDeclarations(declarations))

  def stmts(): Seq[Stmt] = loop.body.ss
}

case class Context(program: Program, method: Method, declarations: Seq[Declaration], atoms: Seq[Exp]) {
  def args(): Seq[LocalVarDecl] = vars().map(v => LocalVarDecl(s"${v.name}_0", v.typ)())

  def vars(): Seq[LocalVarDecl] = declarations.collect { case v: LocalVarDecl => v }

  def fields(): Seq[Field] = program.fields

  def addDeclarations(declarations: Seq[Declaration]): Context = copy(declarations = this.declarations ++ declarations)
}
