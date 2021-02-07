package rpi.inference.context

import rpi.Names
import rpi.builder.ProgramBuilder
import rpi.inference.annotation.Annotation
import rpi.util.Namespace
import viper.silver.ast

import scala.collection.mutable
import scala.collection.mutable.ListBuffer

class CheckBuilder(program: ast.Program) extends ProgramBuilder {

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
    specification.asInstance
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
        // loop instrumentation
        addInstrumented {
          val check = createCheck(original, declarations)
          addExhale(check.invariant)
          addCut(original, check)
          addInhale(check.invariant)
          addInhale(makeNot(condition))
        }
      case original@ast.MethodCall(name, arguments, returns) =>
        if (Names.isAnnotation(name)) {
          val annotation = Annotation(name, arguments.head)
          annotations.append(annotation)
        } else {
          // make sure all arguments are variables
          val variables = arguments.map {
            case variable: ast.LocalVar =>
              variable
            case field: ast.FieldAccess =>
              // create auxiliary variable
              val name = namespace.uniqueIdentifier("t", Some(0))
              val variable = makeVariable(name, field.typ)
              // add annotation
              val annotation = Annotation(Names.downAnnotation, variable)
              annotations.append(annotation)
              // assign to variable and return variable
              addAssign(variable, field)
              variable
            case argument =>
              sys.error(s"Unexpected argument: $argument")
          }
          val adapted = original.copy(args = variables)(original.pos, original.info, original.errT)
          // method call instrumentation
          addInstrumented {
            val check = methods(name)
            addExhale(check.precondition(variables))
            addCut(adapted, check)
            addInhale(check.postcondition(variables ++ returns))
          }
        }
      case _ =>
        addStatement(statement)
    }

  private def addInhale(instance: Instance): Unit =
    instance.all.foreach { expression => addInhale(expression) }

  private def addExhale(instance: Instance): Unit =
    instance.all.foreach { expression => addExhale(expression) }

  private def addInstrumented(generate: => Unit): Unit = {
    val consumed = consumeAnnotations()
    val body = makeScope(generate)
    addStatement(makeInstrument(body, consumed))
  }

  private def addCut(statement: ast.Stmt, check: Check): Unit =
    addStatement(makeCut(statement, check))

  private def consumeAnnotations(): Seq[Annotation] = {
    val consumed = annotations.toSeq
    annotations.clear()
    consumed
  }
}
