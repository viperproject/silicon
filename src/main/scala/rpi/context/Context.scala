package rpi.context

import rpi.builder.ProgramBuilder
import rpi.{Configuration, Names}
import rpi.inference._
import rpi.teacher.query._
import rpi.util.Expressions.makeNot
import rpi.util.Infos.CheckInfo
import rpi.util.Namespace
import viper.silver.ast
import viper.silver.verifier.Verifier

import scala.collection.mutable
import scala.collection.mutable.ListBuffer

/**
  * Context information used by the inference.
  *
  * @param inference The inference.
  * @param input     The the input program.
  */
class Context(inference: Inference, val input: ast.Program) {
  /**
    * Returns the configuration.
    *
    * @return The configuration.
    */
  def configuration: Configuration =
    inference.configuration

  /**
    * Returns the verifier.
    *
    * @return The verifier.
    */
  def verifier: Verifier =
    inference.verifier

  private val builder =
    new CheckBuilder(input)

  private val checks: Seq[Seq[Check]] = {
    val all = builder.checks.toSeq
    if (configuration.noBatching()) all.map { check => Seq(check) }
    else Seq(all)
  }

  private val specifications: Map[String, Specification] = {
    // get specifications from check builder
    val buffer = builder.specifications

    // add specification for recursive predicate
    if (configuration.usePredicates()) {
      val names = if (configuration.useSegments()) Seq("x", "y") else Seq("x")
      val parameters = names.map { name => ast.LocalVarDecl(name, ast.Ref)() }
      val atoms = this.atoms.fromParameters(parameters.take(1))
      buffer.append(Specification(Names.recursive, parameters, atoms))
    }

    // add specifications for append lemma
    if (configuration.useSegments()) {
      val names = Seq("x", "y", "z")
      val parameters = names.map { name => ast.LocalVarDecl(name, ast.Ref)() }
      val atoms = this.atoms.fromParameters(parameters.slice(1, 2))
      buffer.append(Specification(Names.appendLemma, parameters, atoms))
    }

    // create map
    buffer
      .map { specification => specification.name -> specification }
      .toMap
  }

  /**
    * Returns a copy of the namespace.
    *
    * @return A copy of the namespace.
    */
  def namespace: Namespace =
    builder.namespace.copy()

  def atoms: Atoms =
    builder.atoms

  def batches: Seq[Seq[Check]] =
    checks

  /**
    * Returns the specification with the given name.
    *
    * @param name The name.
    * @return The specification.
    */
  def specification(name: String): Specification =
    specifications(name)

  /**
    * Returns an instance of the specifications with the given name with the given arguments.
    *
    * @param name      The name of the specification.
    * @param arguments The arguments.
    * @return The instance.
    */
  def instance(name: String, arguments: Seq[ast.Exp]): Instance = {
    Instance(specification(name), arguments)
  }

  /**
    * Returns an instance of the specifications corresponding to the given placeholder predicate.
    *
    * @param placeholder The placeholder predicate.
    * @return The instance.
    */
  def instance(placeholder: ast.PredicateAccess): Instance =
    instance(placeholder.predicateName, placeholder.args)

  // TODO:
  def predicates(hypothesis: Hypothesis): Seq[ast.Predicate] = ???
}

private class CheckBuilder(program: ast.Program) extends ProgramBuilder {
  /**
    * The atoms.
    */
  val atoms: Atoms = new Atoms(program)

  /**
    * The namespace used to generate unique identifiers.
    */
  val namespace: Namespace =
    new Namespace

  val specifications: mutable.Buffer[Specification] =
    ListBuffer.empty

  val checks: mutable.Buffer[Check] =
    ListBuffer.empty

  val methods: Map[String, MethodCheck] =
    program
      .methods
      .map { method => method.name -> createCheck(method) }
      .toMap

  process()

  private def process(): Unit = {
    program
      .methods
      .foreach { method =>
        val check = methods(method.name)
        createBody(check, method.body.get, method.formalArgs ++ method.formalReturns)
      }
  }

  private def createSpecification(prefix: String, parameters: Seq[ast.LocalVarDecl], existing: Seq[ast.Exp]): Specification = {
    val name = namespace.uniqueIdentifier(prefix, Some(0))
    val atoms = this.atoms.fromParameters(parameters)
    val specification = Specification(name, parameters, atoms, existing)
    // add and return specification
    specifications.append(specification)
    specification
  }

  private def createCheck(method: ast.Method): MethodCheck = {
    // create method check
    val name = namespace.uniqueIdentifier(s"check_${method.name}")
    val precondition = createSpecification(Names.precondition, method.formalArgs, method.pres)
    val postcondition = createSpecification(Names.postcondition, method.formalArgs ++ method.formalReturns, method.posts)
    val check = new MethodCheck(name, precondition, postcondition)
    // add and return check
    checks.append(check)
    check
  }

  private def createBody(check: MethodCheck, sequence: ast.Seqn, declarations: Seq[ast.LocalVarDecl]): Unit = {
    val body = makeScope {
      // inhale method preconditions
      addInstrumented {
        val preconditions = check.precondition.all
        preconditions.foreach { expression => addInhale(expression) }
      }
      // process body
      val processed = processSequence(sequence, declarations)
      addStatement(processed)
      // exhale method postconditions
      addInstrumented {
        val postconditions = check.postcondition.all
        postconditions.foreach { expression => addExhale(expression) }
      }
    }
    check.setBody(body)
  }

  private def createCheck(loop: ast.While, declarations: Seq[ast.LocalVarDecl]): LoopCheck = {
    // create loop check
    val name = namespace.uniqueIdentifier(s"check", Some(0))
    val invariant = createSpecification(Names.invariant, declarations, loop.invs)
    val check = new LoopCheck(name, invariant)
    // add check body
    val body = makeScope {
      // inhale loop invariants and condition
      addInstrumented {
        val invariants = invariant.all
        invariants.foreach { expression => addInhale(expression) }
        addInhale(loop.cond)
      }
      // process body
      val processed = processSequence(loop.body, declarations)
      addStatement(processed)
      // exhale loop invariants
      addInstrumented {
        val invariants = invariant.all
        invariants.foreach { expression => addExhale(expression) }
      }
    }
    check.setBody(body)
    // add and return check
    checks.append(check)
    check
  }

  private def processSequence(sequence: ast.Seqn, declarations: Seq[ast.LocalVarDecl]): ast.Seqn = {
    val variables = sequence.scopedDecls.collect { case variable: ast.LocalVarDecl => variable }
    val all = declarations ++ variables
    val statements = scoped {
      sequence.ss.foreach { statement => processStatement(statement, all) }
    }
    sequence.copy(ss = statements)(sequence.pos, sequence.info, sequence.errT)
  }

  private def processStatement(statement: ast.Stmt, declarations: Seq[ast.LocalVarDecl]): Unit =
    statement match {
      case sequence: ast.Seqn =>
        val processed = processSequence(sequence, declarations)
        addStatement(processed)
      case conditional: ast.If =>
        // process both branches
        val thenBranch = processSequence(conditional.thn, declarations)
        val elseBranch = processSequence(conditional.els, declarations)
        // update conditional
        val processed = conditional.copy(thn = thenBranch, els = elseBranch)(conditional.pos, conditional.info, conditional.errT)
        addStatement(processed)
      case loop: ast.While =>
        val check = createCheck(loop, declarations)
        // loop instrumentation
        addInstrumented {
          // TODO: Havoc
          val invariants = check.invariant.all
          invariants.foreach { expression => addExhale(expression) }
          invariants.foreach { expression => addInhale(expression) }
          addInhale(makeNot(loop.cond))
        }
      case call: ast.MethodCall => // TODO: Implement me.
      case _ =>
        addStatement(statement)
    }

  private def addInstrumented(generate: => Unit): Unit = {
    val body = makeScope(generate)
    addStatement(Instrument(body))
  }

}