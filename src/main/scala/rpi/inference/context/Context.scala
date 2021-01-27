package rpi.inference.context

import rpi.builder.ProgramBuilder
import rpi.{Configuration, Names, inference}
import rpi.inference._
import rpi.inference.annotation.Annotation
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

  /**
    * Returns the atoms.
    *
    * @return The atoms.
    */
  def atoms: Atoms =
    builder.atoms

  /**
    * Returns the check corresponding to the method with the given name.
    *
    * @param name The name of the method.
    * @return The check.
    */
  def check(name: String): MethodCheck =
    builder.methods(name)

  /**
    * Returns the checks as a sequence of batches that are meant to be checked together.
    *
    * @return The batches.
    */
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
    BindingInstance(specification(name), arguments)
  }

  /**
    * Returns an instance of the specifications corresponding to the given predicate access.
    *
    * @param access The predicate access.
    * @return The instance.
    */
  def instance(access: ast.PredicateAccess): Instance =
    instance(access.predicateName, access.args)
}

private class CheckBuilder(program: ast.Program) extends ProgramBuilder {

  import rpi.util.ast.Expressions._
  import rpi.util.ast.Statements._

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

  // TODO: Implement properly.
  val annotations: mutable.Buffer[Annotation] =
    ListBuffer.empty

  process()

  private def process(): Unit = {
    program
      .methods
      .foreach { method =>
        val check = methods(method.name)
        createBody(check, method.body.get, method.formalArgs ++ method.formalReturns)
      }

    checks.foreach { check =>
      println(check.name)
      println(check.body)
    }
  }

  private def createSpecification(prefix: String, parameters: Seq[ast.LocalVarDecl], existing: Seq[ast.Exp]): Instance = {
    val name = namespace.uniqueIdentifier(prefix, Some(0))
    val atoms = this.atoms.fromParameters(parameters)
    val specification = Specification(name, parameters, atoms, existing)
    // add and return specification
    specifications.append(specification)
    IdentityInstance(specification)
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
      addInstrumented(addInhale(check.precondition))
      // process body
      val processed = processSequence(sequence, declarations)
      addStatement(processed)
      // exhale method postconditions
      addInstrumented(addExhale(check.postcondition))
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
        addInhale(invariant)
        addInhale(loop.cond)
      }
      // process body
      val processed = processSequence(loop.body, declarations)
      addStatement(processed)
      // exhale loop invariants
      addInstrumented(addExhale(invariant))
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
      case original@ast.If(_, thenBranch, elseBranch) =>
        // process both branches
        val processedThen = processSequence(thenBranch, declarations)
        val processedElse = processSequence(elseBranch, declarations)
        // update conditional
        val processed = original.copy(thn = processedThen, els = processedElse)(original.pos, original.info, original.errT)
        addStatement(processed)
      case original@ast.While(condition, _, _) =>
        val check = createCheck(original, declarations)
        // loop instrumentation
        addInstrumented {
          addExhale(check.invariant)
          addCut(original, check)
          addInhale(check.invariant)
          addInhale(makeNot(condition))
        }
      case ast.MethodCall(name, arguments, _) =>
        if (Names.isAnnotation(name)) {
          val annotation = inference.annotation.Annotation(name, arguments.head)
          annotations.append(annotation)
        } else {
          // TODO: Implement me.
          ???
        }
      case _ =>
        addStatement(statement)
    }

  private def addInhale(instance: Instance): Unit =
    instance.all.foreach { expression => addInhale(expression) }

  private def addExhale(instance: Instance): Unit =
    instance.all.foreach { expression => addExhale(expression) }

  private def addInstrumented(generate: => Unit): Unit = {
    val body = makeScope(generate)
    addStatement(makeInstrument(body, annotations.toSeq))
    annotations.clear()
  }

  private def addCut(statement: ast.Stmt, check: Check): Unit =
    addStatement(makeCut(statement, check))
}