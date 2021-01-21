package rpi.inference

import rpi.{Main, Names, Settings}
import rpi.learner.Learner
import rpi.teacher.Teacher
import rpi.util.{Collections, Expressions, Namespace}
import viper.silicon.Silicon
import viper.silver.ast
import viper.silver.ast.utility.rewriter.Traverse
import viper.silver.verifier.{VerificationResult, Verifier}

import scala.annotation.tailrec
import scala.collection.mutable
import scala.collection.mutable.ListBuffer

class Inference() {
  /**
    * The magic fields that enables fold / unfold heuristics
    */
  val magic: ast.Field = ast.Field("__CONFIG_HEURISTICS", ast.Bool)()

  /**
    * The instance of the silicon verifier used to generate the samples.
    */
  private val verifier: Verifier = {
    // create instance
    val instance = new Silicon()
    // pass arguments
    val arguments = Seq(
      "--z3Exe", Main.z3,
      "--counterexample", "raw",
      "--ignoreFile", "dummy.vpr")
    instance.parseCommandLine(arguments)
    // return instance
    instance
  }

  /**
    * Starts the inference and all of its subcomponents.
    */
  def start(): Unit = {
    verifier.start()
  }

  /**
    * Stops the inference and all of its subcomponents.
    */
  def stop(): Unit = {
    verifier.stop()
  }

  def run(program: ast.Program): ast.Program = {

    val context = new Context(inference = this, program)

    val teacher = new Teacher(context)
    val learner = new Learner(context)


    teacher.start()
    learner.start()

    @tailrec
    def infer(rounds: Int): Hypothesis = {
      // compute hypothesis
      val hypothesis = learner.hypothesis
      if (rounds == 0) hypothesis
      else {
        println(s"----- round ${Settings.maxRounds - rounds} -----")
        // check hypothesis
        val samples = teacher.check(hypothesis)
        if (samples.isEmpty) hypothesis
        else {
          // add samples and iterate
          samples.foreach { sample => learner.addSample(sample) }
          infer(rounds - 1)
        }
      }
    }

    val hypothesis = infer(Settings.maxRounds)

    teacher.stop()
    learner.stop()

    annotate(context, hypothesis)
  }

  /**
    * Verifies the given program.
    *
    * @param program The program to verify.
    * @return The verification result.
    */
  def verify(program: ast.Program): VerificationResult =
    verifier.verify(program)

  private def annotate(context: Context, hypothesis: Hypothesis): ast.Program = {
    val program = context.program

    // helper method that replaces predicates with the inferred specification
    def substitute(expression: ast.Exp): ast.Exp =
      expression match {
        case ast.PredicateAccessPredicate(predicate, _) =>
          val instance = {
            val name = predicate.predicateName
            val arguments = predicate.args
            context.getInstance(name, arguments)
          }
          hypothesis.getPredicateBody(instance)
        case _ => expression
      }

    // create fields
    val fields = magic +: program.fields
    // create predicates
    val predicates = {
      val existing = program.predicates
      val inferred = hypothesis.getPredicate(Names.recursive).toSeq
      existing ++ inferred
    }
    // annotate methods
    val methods = program
      .methods
      .map { method =>
        val preconditions = method.pres.map { precondition => substitute(precondition) }
        val postconditions = method.posts.map { postcondition => substitute(postcondition) }
        val body = method.body.map { sequence =>
          sequence.transform({
            case ast.While(condition, invariants, body) =>
              val substituted = invariants.map { invariant => substitute(invariant) }
              ast.While(condition, substituted, body)()
            case ast.MethodCall(name, _, _) if Names.isAnnotation(name) =>
              // TODO: Handle annotations.
              ast.Seqn(Seq.empty, Seq.empty)()
          }, Traverse.BottomUp)
        }
        // create annotated method
        ast.Method(method.name, method.formalArgs, method.formalReturns, preconditions, postconditions, body)()
      }
    // return annotated program
    ast.Program(program.domains, fields, program.functions, predicates, methods, program.extensions)()
  }
}

class Context(val inference: Inference, val program: ast.Program) {
  /**
    * The namespace used to create unique identifiers.
    */
  private val namespace = new Namespace()

  /**
    * The templates for the atomic predicates.
    */
  private val templates = {
    // TODO: Implement properly.
    val x0 = ast.LocalVarDecl("x0", ast.Ref)()
    val x1 = ast.LocalVarDecl("x1", ast.Ref)()
    val t0 = ast.Predicate("t0", Seq(x0), Some(ast.NeCmp(x0.localVar, ast.NullLit()())()))()
    val t1 = ast.Predicate("t1", Seq(x0, x1), Some(ast.NeCmp(x0.localVar, x1.localVar)()))()
    Seq(t0, t1)
  }

  /**
    * Instantiates the atomic predicate templates with the given arguments.
    *
    * @param arguments The arguments.
    * @return The instantiated atomic predicates.
    */
  def instantiateAtoms(arguments: Seq[ast.Exp]): Seq[ast.Exp] =
    templates.flatMap { template =>
      template.formalArgs.length match {
        case 1 => arguments
          .map { variable =>
            Expressions.instantiate(template, Seq(variable))
          }
        case 2 => Collections
          .pairs(arguments)
          .map { case (first, second) =>
            Expressions.instantiate(template, Seq(first, second))
          }
      }
    }

  /**
    * The program labeled with all holes plus the map containing all holes.
    */
  private val (_labeled, specifications) = {
    // initialize map
    val buffer: mutable.Buffer[Specification] = ListBuffer.empty

    // helper method to create predicate accessing a specification
    def create(prefix: String, parameters: Seq[ast.LocalVarDecl]): ast.PredicateAccessPredicate = {
      // rename parameters
      val renamed =
        if (Settings.renameParameters) parameters
          .zipWithIndex
          .map { case (parameter, index) => ast.LocalVarDecl(s"x_$index", parameter.typ)() }
        else parameters
      // create specification
      val name = namespace.uniqueIdentifier(prefix, Some(0))
      val references = renamed
        .filter { parameter => parameter.typ == ast.Ref }
        .map { parameter => parameter.localVar }
      val atoms = instantiateAtoms(references)
      val specification = Specification(name, renamed, atoms)
      buffer.append(specification)
      // predicate access
      val arguments = parameters.map { parameter => parameter.localVar }
      val access = ast.PredicateAccess(arguments, name)()
      val instance = Instance(specification, arguments)
      val info = InstanceInfo(instance)
      ast.PredicateAccessPredicate(access, ast.FullPerm()())(info = info)
    }

    // add specification for recursive predicate
    if (Settings.useRecursion) {
      val names = if (Settings.useSegments) Seq("x", "y") else Seq("x")
      val parameters = names.map { name => ast.LocalVarDecl(name, ast.Ref)() }
      val variables = parameters.take(1).map { parameter => parameter.localVar }
      val atoms = instantiateAtoms(variables)
      buffer.append(Specification(Names.recursive, parameters, atoms))
    }

    // add specifications for append lemma
    if (Settings.useSegments) {
      val names = Seq("x", "y", "z")
      val parameters = names.map { name => ast.LocalVarDecl(name, ast.Ref)() }
      val variables = parameters.slice(1, 2).map { parameter => parameter.localVar }
      val atoms = instantiateAtoms(variables)
      buffer.append(Specification(Names.appendLemma, parameters, atoms))
    }

    // labels all positions of the program for which specifications need to be inferred
    val labeled = program.transformWithContext[Seq[ast.LocalVarDecl]]({
      case (method: ast.Method, _) =>
        val variables = method.formalArgs
        val preconditions = create(Names.precondition, variables) +: method.pres
        val postconditions = create(Names.postcondition, variables) +: method.posts
        val transformed = method.copy(pres = preconditions, posts = postconditions)(method.pos, method.info, method.errT)
        (transformed, variables)
      case (loop: ast.While, variables) =>
        val invariants = create(Names.invariant, variables) +: loop.invs
        val transformed = loop.copy(invs = invariants)(loop.pos, loop.info, loop.errT)
        (transformed, variables)
      case (sequence: ast.Seqn, variables) =>
        val declarations = sequence.scopedDecls.collect { case variable: ast.LocalVarDecl => variable }
        (sequence, variables ++ declarations)
    }, Seq.empty, Traverse.TopDown)

    // create specification map
    val specifications = buffer
      .map { specification => specification.name -> specification }
      .toMap

    (labeled, specifications)
  }

  def labeled: ast.Program = _labeled

  def predicates(hypothesis: Hypothesis): Seq[ast.Predicate] = {
    // get all specifications
    val all =
      if (Settings.inline) specifications.get(Names.recursive).toSeq
      else specifications.values.filter { specification => specification.name != Names.appendLemma }
    // create predicates
    all
      .map { specification => hypothesis.getPredicate(specification) }
      .toSeq
  }

  /**
    * Returns the specification with the given name.
    *
    * @param name The name of the specification.
    * @return The specifications.
    */
  def getSpecification(name: String): Specification =
    specifications(name)

  /**
    * Returns an instance of the specifications with the given name and arguments.
    *
    * @param name      The name of the specification.
    * @param arguments The arguments with which the specifications should be instantiated.
    * @return The instance.
    */
  def getInstance(name: String, arguments: Seq[ast.Exp]): Instance = {
    val specification = getSpecification(name)
    Instance(specification, arguments)
  }
}