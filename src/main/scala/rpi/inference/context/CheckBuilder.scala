package rpi.inference.context

import rpi.Names
import rpi.builder.ProgramBuilder
import rpi.inference.annotation.Hint
import rpi.util.Namespace
import rpi.util.ast.Expressions._
import rpi.util.ast.Statements._
import viper.silver.ast

import scala.collection.mutable
import scala.collection.mutable.ListBuffer

class CheckBuilder(program: ast.Program) extends ProgramBuilder {

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

  var hints: Seq[Hint] = _

  process()

  private def process(): Unit =
    program
      .methods
      .foreach { method =>
        val check = methods(method.name)
        createBody(check, method.body.get, method.formalArgs ++ method.formalReturns)
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
    clear()
    val body = makeScope {
      // inhale method preconditions
      hinted(addInhale(check.precondition))
      // process body
      val processed = processSequence(sequence, declarations)
      addStatement(processed)
      // exhale method postconditions
      hinted(addExhale(check.postcondition))
    }
    check.setBody(body)
  }

  private def createCheck(loop: ast.While, declarations: Seq[ast.LocalVarDecl]): LoopCheck = {
    // create loop check
    val name = namespace.uniqueIdentifier(s"check", Some(0))
    val invariant = createSpecification(Names.invariant, declarations, loop.invs)
    val check = new LoopCheck(name, invariant)
    // add check body
    clear()
    val body = makeScope {
      // inhale loop invariants and condition
      hinted {
        addInhale(invariant)
        addInhale(loop.cond)
      }
      // process body
      val processed = processSequence(loop.body, declarations)
      addStatement(processed)
      // exhale loop invariants
      hinted(addExhale(invariant))
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
        // save hints
        val outerHints = consumeHints()
        // process then branch
        val thenProcessed = processSequence(thenBranch, declarations)
        val thenHints = consumeHints()
        // process else branch
        val elseProcessed = processSequence(elseBranch, declarations)
        val elseHints = consumeHints()
        // restore hints
        hints = outerHints
        // handle condition
        val condition =
          if (thenHints.isEmpty && elseHints.isEmpty) original.cond
          else {
            // update inner hints
            val condition = save(original.cond)
            thenHints.foreach { hint => addHint(hint.withCondition(condition)) }
            elseHints.foreach { hint => addHint(hint.withCondition(makeNot(condition))) }
            // return condition
            condition
          }
        // update conditional
        val processed = original.copy(cond = condition, thn = thenProcessed, els = elseProcessed)(original.pos, original.info, original.errT)
        addStatement(processed)
      case original@ast.While(condition, _, _) =>
        // loop instrumentation
        val check = createCheck(original, declarations)
        // exhale invariant
        hinted(addExhale(check.invariant))
        // cut loop (havoc written variables)
        // TODO: havoc hints
        addCut(original, check)
        // inhale invariant and negation of loop condition
        hinted {
          addInhale(check.invariant)
          addInhale(makeNot(condition))
        }
      case original@ast.MethodCall(name, arguments, returns) =>
        if (Names.isAnnotation(name)) {
          val argument = arguments.head
          val old = save(argument)
          val hint = Hint(name, argument, old)
          addHint(hint)
        } else {
          // make sure all arguments are variables
          val variables = arguments.map {
            case variable: ast.LocalVar =>
              variable
            case field: ast.FieldAccess =>
              // create variable
              val variable = save(field)
              // add hint
              val old = asVariable(field.rcv)
              val hint = Hint(Names.downAnnotation, variable, old)
              addHint(hint)
              // return variable
              variable
            case argument =>
              sys.error(s"Unexpected argument: $argument")
          }
          val adapted = original.copy(args = variables)(original.pos, original.info, original.errT)
          // method call instrumentation
          val check = methods(name)
          // exhale method precondition
          hinted(addExhale(check.precondition(variables)))
          // havoc return variables
          // TODO: havoc hints
          addCut(adapted, check)
          // inhale method postcondition
          hinted(addInhale(check.postcondition(variables ++ returns)))
        }
      case _ =>
        addStatement(statement)
    }

  private def clear(): Unit = {
    hints = Seq.empty
  }

  private def asVariable(expression: ast.Exp): ast.LocalVar =
    expression match {
      case variable: ast.LocalVar => variable
      case _ => ???
    }

  private def save(expression: ast.Exp): ast.LocalVar = {
    // create variable
    val name = namespace.uniqueIdentifier("t", Some(0))
    val variable = makeVariable(name, expression.typ)
    // add assignment
    addAssign(variable, expression)
    // return variable
    variable
  }

  private def addInhale(instance: Instance): Unit =
    instance.all.foreach { expression => addInhale(expression) }

  private def addExhale(instance: Instance): Unit =
    instance.all.foreach { expression => addExhale(expression) }

  private def hinted(generate: => Unit): Unit = {
    val hints = this.hints
    val body = makeScope(generate)
    addStatement(makeHinted(body, hints))
  }

  private def addCut(statement: ast.Stmt, check: Check): Unit =
    addStatement(makeCut(statement, check))

  private def addHint(hint: Hint): Unit =
    hints = hints :+ hint

  private def consumeHints(): Seq[Hint] = {
    val consumed = hints
    hints = Seq.empty
    consumed
  }
}
