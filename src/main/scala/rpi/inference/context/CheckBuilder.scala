// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package rpi.inference.context

import rpi.Names
import rpi.builder.ProgramBuilder
import rpi.inference.annotation.Hint
import rpi.util.Namespace
import rpi.util.ast.Expressions._
import rpi.util.ast.Previous
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
    val body = makeScope {
      // inhale method preconditions
      hinted(Seq.empty) {
        addInhale(check.precondition)
      }
      // process body
      val (processed, hints) = processSequence(sequence, declarations)
      addStatement(processed)
      // exhale method postconditions
      hinted(hints) {
        addExhale(check.postcondition)
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
      hinted(Seq.empty) {
        addInhale(invariant)
        addInhale(loop.cond)
      }
      // process body
      val (processed, hints) = processSequence(loop.body, declarations)
      addStatement(processed)
      // exhale loop invariants
      hinted(hints) {
        addExhale(invariant)
      }
    }
    check.setBody(body)
    // add and return check
    checks.append(check)
    check
  }

  /**
    * Processes the given sequence and returns the updated sequence and the list of hints that were collected.
    *
    * @param sequence     The sequence to process.
    * @param declarations The declarations.
    * @return The updated sequence and the collected hints.
    */
  private def processSequence(sequence: ast.Seqn, declarations: Seq[ast.LocalVarDecl]): (ast.Seqn, Seq[Hint]) = {
    // save and reset hints
    val savedHints = this.hints
    this.hints = Seq.empty
    // process and update sequence
    val statements = scoped {
      // add scoped declarations
      val variables = sequence.scopedDecls.collect { case variable: ast.LocalVarDecl => variable }
      val all = declarations ++ variables
      // process statements
      sequence.ss.foreach { statement => processStatement(statement, all) }
    }
    val processed = sequence.copy(ss = statements)(sequence.pos, sequence.info, sequence.errT)
    // extract and restore hints
    val hints = this.hints
    this.hints = savedHints
    // return processed sequence and hints
    (processed, hints)
  }

  private def processStatement(statement: ast.Stmt, declarations: Seq[ast.LocalVarDecl]): Unit =
    statement match {
      case sequence: ast.Seqn =>
        val (processed, innerHints) = processSequence(sequence, declarations)
        addStatement(processed)
        innerHints.foreach { hint => addHint(hint) }
      case original@ast.If(_, thenBranch, elseBranch) =>
        // process branches
        val (thenProcessed, thenHints) = processSequence(thenBranch, declarations)
        val (elseProcessed, elseHints) = processSequence(elseBranch, declarations)
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
        hinted(hints) {
          addExhale(check.invariant)
        }
        // cut loop (havoc written variables)
        addCut(original, check)
        // inhale invariant and negation of loop condition
        hinted(hints) {
          addInhale(check.invariant)
          addInhale(makeNot(condition))
        }
      case original@ast.MethodCall(name, arguments, returns) =>
        if (Names.isAnnotation(name)) {
          val argument = arguments.head
          val old = save(argument, Previous(argument))
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
          hinted(hints) {
            addExhale(check.precondition(variables))
          }
          // havoc return variables
          addCut(adapted, check)
          // inhale method postcondition
          hinted(hints) {
            addInhale(check.postcondition(variables ++ returns))
          }
        }
      case _ =>
        addStatement(statement)
    }

  private def asVariable(expression: ast.Exp): ast.LocalVar =
    expression match {
      case variable: ast.LocalVar => variable
      case _ => ???
    }

  private def save(expression: ast.Exp, info: ast.Info = ast.NoInfo): ast.LocalVar = {
    // create variable
    val name = namespace.uniqueIdentifier("t", Some(0))
    val variable = makeVariable(name, expression.typ, info)
    // add assignment
    addAssign(variable, expression)
    // return variable
    variable
  }

  private def addInhale(instance: Instance): Unit =
    instance.all.foreach { expression => addInhale(expression) }

  private def addExhale(instance: Instance): Unit =
    instance.all.foreach { expression => addExhale(expression) }

  private def hinted(hints: Seq[Hint])(generate: => Unit): Unit = {
    val body = makeScope(generate)
    addStatement(makeHinted(body, hints))
  }

  private def addCut(statement: ast.Stmt, check: Check): Unit = {
    // create cut
    val cut = makeCut(statement, check)
    // havoc hints
    hints = hints.filter { hint =>
      hint.argument match {
        case variable: ast.LocalVar =>
          !cut.havocked.contains(variable)
        case _ =>
          true
      }
    }
    // add cut
    addStatement(cut)
  }

  private def addHint(hint: Hint): Unit =
    hints = hints :+ hint
}
