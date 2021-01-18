package rpi.teacher

import rpi.{Names, Settings}
import rpi.inference._
import rpi.util.Namespace
import viper.silver.ast

import scala.collection.mutable
import scala.collection.mutable.ListBuffer

/**
  * Builds programs used to check hypotheses.
  *
  * @param teacher The pointer to the teacher.
  */
class CheckBuilder(teacher: Teacher) {

  import rpi.util.Expressions._
  import rpi.util.Statements._

  /**
    * Returns the pointer to the inference.
    *
    * @return The pointer to the inference.
    */
  private def inference: Inference = teacher.inference

  /**
    * Returns the pointer to the original program (labeled).
    *
    * @return The pointer to the original program.
    */
  private def original: ast.Program = inference.labeled

  /**
    * The namespace used to generate unique identifiers.
    */
  private var namespace: Namespace = _

  /**
    * The context information for the sample extractor.
    */
  private var context: Context = _

  /**
    * The stack of statement buffers used to accumulate the instrumented statements. The stack is required to properly
    * handle control flow. The topmost buffer accumulates statements for the current branch.
    */
  private var stack: List[mutable.Buffer[ast.Stmt]] = _

  /**
    * Returns a program that performs self-framing checks for the given hypothesis.
    *
    * @param hypothesis The hypothesis to check for self-framingness.
    * @return The program and the context object.
    */
  def framingChecks(hypothesis: Hypothesis): (ast.Program, Context) = {
    /**
      * Helper method that inhales the given expression conjunct-wise. The expression is implicitly rewritten to have
      * its conjuncts at the top level by pushing implications inside.
      *
      * @param expression The expression to inhale.
      * @param guards     The guards guarding the current expression.
      */
    def addInhales(expression: ast.Exp, guards: Seq[ast.Exp] = Seq.empty): Unit =
      expression match {
        case ast.And(left, right) =>
          addInhales(left, guards)
          addInhales(right, guards)
        case ast.Implies(guard, guarded) =>
          addInhales(guarded, guards :+ guard)
        case conjunct =>
          // compute info used to extract framing sample
          val info = conjunct match {
            case ast.FieldAccessPredicate(location, _) => FramingInfo(location)
            case ast.PredicateAccessPredicate(location, _) => FramingInfo(location)
            case _ => ast.NoInfo
          }
          // inhale part
          val condition = implies(bigAnd(guards), conjunct)
          val inhale = ast.Inhale(condition)(info = info)
          addStatement(inhale)
      }

    // create a check for each specification predicate
    clear()
    val checks = hypothesis
      .predicates
      .map { case (name, predicate) =>
        push()
        // save state
        val arguments = predicate.formalArgs.map { parameter => parameter.localVar }
        val instance = inference.getInstance(name, arguments)
        val label = saveState(instance)
        context.addSnapshot(label, instance)
        // inhale inferred specification
        val inferred = hypothesis.get(instance)
        addInhales(inferred)
        // return check
        pop()
      }
      .toSeq

    // return program
    val dummy = Hypothesis(Map.empty)
    val program = buildProgram(checks, dummy)
    (program, context)
  }

  /**
    * Returns a program that performs the given checks.
    * @param checks     The checks.
    * @param hypothesis The hypothesis.
    * @return The program and the context object.
    */
  def basicChecks(checks: Seq[Check], hypothesis: Hypothesis): (ast.Program, Context) = {
    // instrument checks
    clear()
    val instrumented = checks.map { check => basicCheck(check, hypothesis) }
    // return program and context
    val program = buildProgram(instrumented, hypothesis)
    (program, context)
  }

  /**
    * Returns the body of a method performing the given check.
    * @param check      The check.
    * @param hypothesis The hypothesis.
    * @return The body.
    */
  private def basicCheck(check: Check, hypothesis: Hypothesis): ast.Seqn = {
    import Names._
    /**
      * Helper method that instruments the given sequence.
      *
      * @param sequence The sequence to instrument.
      * @return The instrumented sequence.
      */
    def instrumentSequence(sequence: ast.Seqn): ast.Seqn = {
      push()
      sequence
        .ss
        .foreach { statement =>
          instrumentStatement(statement)
        }
      pop()
    }

    /**
      * Helper method that instruments the given statement.
      *
      * @param statement The statement to instrument.
      */
    def instrumentStatement(statement: ast.Stmt): Unit =
      statement match {
        case ast.If(condition, thenBody, elseBody) =>
          // instrument branches
          val thenInstrumented = instrumentSequence(thenBody)
          val elseInstrumented = instrumentSequence(elseBody)
          // add instrumented conditional
          val instrumented = ast.If(condition, thenInstrumented, elseInstrumented)()
          addStatement(instrumented)
        case ast.Inhale(expression) => expression match {
          case condition if condition.isPure =>
            // inhale pure conditions (presumably non-specification)
            addStatement(ast.Inhale(condition)())
          case predicate: ast.PredicateAccessPredicate =>
            // get annotations
            implicit val annotations: Seq[Annotation] = Annotations.extract(statement)
            // get specification
            val instance = getInstance(predicate)
            val body = hypothesis.get(instance)
            // inhale predicate
            if (Settings.inline) {
              // inhale body of specification predicate
              val info = ast.SimpleInfo(Seq(instance.toString))
              addStatement(ast.Inhale(body)(info = info))
            } else {
              // inhale and unfold specification predicate
              val adapted = {
                val name = instance.name
                val arguments = instance.arguments
                val access = ast.PredicateAccess(arguments, name)()
                ast.PredicateAccessPredicate(access, predicate.perm)()
              }
              addStatement(ast.Inhale(adapted)())
              addStatement(ast.Unfold(adapted)())
            }
            // unfold predicate
            unfold(body, check.unfoldDepth)
            // save state
            val label = saveState(instance)
            context.addSnapshot(label, instance)
        }
        case ast.Exhale(expression) => expression match {
          case condition if condition.isPure =>
            // exhale pure conditions (presumably non-specification)
            addStatement(ast.Exhale(condition)())
          case predicate: ast.PredicateAccessPredicate =>
            // get annotations
            implicit val annotations: Seq[Annotation] = Annotations.extract(statement)
            // get specification
            val instance = getInstance(predicate)
            val body = hypothesis.get(instance)
            // save state
            implicit val label: String = saveState(instance)
            context.addSnapshot(label, instance)
            // save ingredients and fold predicate
            saveAndFold(body, check.foldDepth)
            // exhale predicate
            val info = BasicInfo(label, instance)
            if (Settings.inline) {
              // exhale body of specification
              addStatement(ast.Exhale(body)(info = info))
            } else {
              // fold and exhale specification predicate
              val adapted = {
                val name = instance.name
                val arguments = instance.arguments
                val access = ast.PredicateAccess(arguments, name)()
                ast.PredicateAccessPredicate(access, predicate.perm)()
              }
              addStatement(ast.Fold(adapted)(info = info))
              addStatement(ast.Exhale(adapted)())
            }
        }
        case ast.MethodCall(name, _, _) if Names.isAnnotation(name) =>
          ???
        case _ =>
          addStatement(statement)
      }

    /**
      * Helper methods used to unfold predicate accesses appearing in the given expression.
      *
      * The implicitly passed list of annotations represents the annotations that have not been processed yet.
      *
      * @param expression  The expression to unfold.
      * @param depth       The depth up to which to unfold.
      * @param guards      The guards collected so far.
      * @param annotations The list of unprocessed annotations.
      */
    def unfold(expression: ast.Exp, depth: Int, guards: Seq[ast.Exp] = Seq.empty)
              (implicit annotations: Seq[Annotation]): Unit =
      expression match {
        case ast.And(left, right) =>
          unfold(left, depth, guards)
          unfold(right, depth, guards)
        case ast.Implies(guard, guarded) =>
          unfold(guarded, depth, guards :+ guard)
        case predicate@ast.PredicateAccessPredicate(ast.PredicateAccess(arguments, name), _) =>
          if (annotations.nonEmpty) {
            // handle annotations (only occur when enabled)
            val condition = {
              val equalities = annotations.map {
                case Annotation(`unfoldDownAnnotation`, Seq(argument)) =>
                  ast.EqCmp(arguments.head, argument)()
              }
              bigOr(equalities)
            }
            val unfolds = conditional(Seq(condition), {
              push()
              unfold(predicate, depth + 1)(Seq.empty)
              pop()
            }, {
              push()
              unfold(predicate, depth)(Seq.empty)
              pop()
            })
            addStatement(conditional(guards, unfolds))
          } else if (depth > 0) {
            // open scope
            push()
            // unfold predicate
            addStatement(ast.Unfold(predicate)())
            // recursively unfold predicates appearing in body
            if (depth > 1) {
              val instance = inference.getInstance(name, arguments)
              val body = hypothesis.get(instance)
              unfold(body, depth - 1)
            }
            // close scope and make unfolds conditional
            val unfolds = pop()
            addStatement(conditional(guards, unfolds))
          }
        case _ => // do nothing
      }

    /**
      * Helper method used to recursively fold predicate accesses appearing in the given expression. Moreover, it also
      * saves the permission amounts held for each of the ingredients.
      *
      * @param expression  The expression to save and fold.
      * @param depth       The depth up to which to fold.
      * @param guards      The guards collected
      * @param label       The label of the current state.
      * @param annotations The list of unprocessed annotations.
      */
    def saveAndFold(expression: ast.Exp, depth: Int, guards: Seq[ast.Exp] = Seq.empty)
                   (implicit label: String, annotations: Seq[Annotation]): Unit =
      expression match {
        case ast.And(left, right) =>
          saveAndFold(left, depth, guards)
          saveAndFold(right, depth, guards)
        case ast.Implies(guard, guarded) =>
          saveAndFold(guarded, depth, guards :+ guard)
        case ast.FieldAccessPredicate(resource, _) =>
          savePermission(resource, guards)
        case predicate@ast.PredicateAccessPredicate(resource@ast.PredicateAccess(arguments, name), _) =>
          if (annotations.nonEmpty) {
            // handle annotations (only occur when enabled)
            // TODO: Actually handle annotations.
            saveAndFold(predicate, depth, guards)(label, Seq.empty)
          } else if (depth > 0) {
            // open scope
            push()
            // recursively fold predicates appearing in body
            val instance = inference.getInstance(name, arguments)
            val body = hypothesis.get(instance)
            saveAndFold(body, depth - 1)
            // fold predicate
            val info = BasicInfo(label, instance)
            addStatement(ast.Fold(predicate)(info = info))
            // close scope and make folds conditional
            val folds = pop()
            addStatement(ast.If(bigAnd(guards), folds, skip)())
          } else {
            savePermission(resource, guards)
          }
        case _ => // do nothing
      }

    // instrument check
    val sequence = asSequence(check.statements)
    instrumentSequence(sequence)
  }

  /**
    * Builds a program with the given checks. Most components are taken over from the original  program.
    *
    * @param checks     The checks.
    * @param hypothesis The hypothesis.
    * @return The program.
    */
  private def buildProgram(checks: Seq[ast.Seqn], hypothesis: Hypothesis): ast.Program = {
    val domains = original.domains
    val fields =
      if (Settings.useAnnotations) original.fields
      else inference.magic +: original.fields
    val functions = original.functions
    val predicates = {
      val existing = original.predicates
      val inferred = inference.predicates(hypothesis)
      existing ++ inferred
    }
    val methods = {
      val lemmaMethods = hypothesis.lemmaMethods
      val checkMethods = checks.map { check => buildMethod(check) }
      lemmaMethods ++ checkMethods
    }
    val extensions = Seq.empty
    val program = ast.Program(domains, fields, functions, predicates, methods, extensions)()
    println(program)
    program
  }

  /**
    * Builds a method performing to the given check.
    *
    * @param check The check.
    * @return The method.
    */
  private def buildMethod(check: ast.Seqn): ast.Method = {
    val name = namespace.uniqueIdentifier(base = "check", Some(0))
    val arguments = Seq.empty
    val returns = Seq.empty
    val preconditions = Seq.empty
    val postconditions = Seq.empty
    val body = {
      val statements = check.ss
      val declarations = check
        .deepCollect { case variable: ast.LocalVar => variable }
        .distinct
        .map { variable => ast.LocalVarDecl(variable.name, variable.typ)() }
      Some(ast.Seqn(statements, declarations)())
    }
    ast.Method(name, arguments, returns, preconditions, postconditions, body)()
  }

  private def getInstance(predicate: ast.PredicateAccessPredicate): Instance = {
    // make sure all arguments are variable accesses
    val access = predicate.loc
    val (arguments, assignments) = {
      val empty = (Seq.empty[ast.LocalVar], Seq.empty[ast.LocalVarAssign])
      access.args.foldLeft(empty) {
        case ((variables, collected), variable: ast.LocalVar) =>
          (variables :+ variable, collected)
        case ((variables, collected), argument) =>
          val name = namespace.uniqueIdentifier(base = "t", Some(0))
          val variable = ast.LocalVar(name, argument.typ)()
          val assignment = ast.LocalVarAssign(variable, argument)()
          (variables :+ variable, collected :+ assignment)
      }
    }

    // TODO: Inhale permissions to make stuff self-framing
    if (!Settings.useFraming) ???
    assignments.foreach { assignment => addStatement(assignment) }

    // create and return instance
    val name = access.predicateName
    inference.getInstance(name, arguments)
  }

  /**
    * Saves the state relevant for the given specification instance.
    *
    * @param instance The instance.
    * @return The label of the state.
    */
  private def saveState(instance: Instance): String = {
    val label = namespace.uniqueIdentifier(base = "s", Some(0))
    // save values of variables
    instance
      .arguments
      .foreach {
        case variable: ast.LocalVar =>
          val name = s"${label}_${variable.name}"
          saveValue(name, variable)
      }
    // save values of atoms
    instance
      .actualAtoms
      .zipWithIndex
      .foreach {
        case (atom, index) =>
          val name = s"${label}_$index"
          saveAtom(name, atom)
      }
    // add label
    addStatement(ast.Label(label, Seq.empty)())
    label
  }

  /**
    * Saves the currently held permission amount for the given resource.
    *
    * @param resource The resource.
    * @param guards   The conditions guarding the resource.
    * @param label    The label of the state under which the name of the variable should be stored.
    */
  private def savePermission(resource: ast.LocationAccess, guards: Seq[ast.Exp])(implicit label: String): Unit = {
    // auxiliary method to extract condition under which we have permission to even talk about this resource
    def extractConditions(resource: ast.Exp): Seq[ast.Exp] =
      resource match {
        case access: ast.FieldAccess =>
          val name = context.getName(label, access)
          val variable = ast.LocalVar(name, ast.Perm)()
          Seq(ast.PermGtCmp(variable, ast.NoPerm()())())
        case _ => Seq.empty
      }

    // compute conditions
    val conditions = {
      val extracted = resource match {
        case ast.FieldAccess(receiver, _) =>
          extractConditions(receiver)
        case ast.PredicateAccess(arguments, _) =>
          arguments.flatMap { argument => extractConditions(argument) }
      }
      guards ++ extracted
    }

    // generate unique name
    val name = namespace.uniqueIdentifier(base = "p", Some(0))
    context.addName(label, resource, name)
    // construct potentially conditional value
    val value = {
      val current = ast.CurrentPerm(resource)()
      if (conditions.isEmpty) current
      else ast.CondExp(bigAnd(conditions), current, ast.NoPerm()())()
    }
    // save value
    saveValue(name, value)
  }

  /**
    * Saves the value of the given atom in a variable with the given name.
    *
    * @param name The name of the variable.
    * @param atom The atom to save.
    */
  private def saveAtom(name: String, atom: ast.Exp): Unit =
    if (Settings.useBranching) {
      // create variable
      val variable = ast.LocalVar(name, ast.Bool)()
      // create conditional
      val thenBody = asSequence(ast.LocalVarAssign(variable, top)())
      val elseBody = asSequence(ast.LocalVarAssign(variable, bottom)())
      addStatement(ast.If(atom, thenBody, elseBody)())
    } else saveValue(name, atom)


  /**
    * Saves the value of the given expression in a variable with the given name.
    *
    * @param name       The name of the variable.
    * @param expression The expression to save.
    */
  private def saveValue(name: String, expression: ast.Exp): Unit = {
    // create variable and assignment
    val variable = ast.LocalVar(name, expression.typ)()
    addStatement(ast.LocalVarAssign(variable, expression)())
  }

  private def addStatement(statement: ast.Stmt): Unit =
    stack.head.append(statement)

  private def clear(): Unit = {
    namespace = new Namespace
    context = new Context
    stack = List.empty
  }

  private def push(): Unit =
    stack = ListBuffer.empty[ast.Stmt] :: stack

  private def pop(): ast.Seqn =
    stack match {
      case head :: tail =>
        stack = tail
        asSequence(head.toSeq)
    }
}