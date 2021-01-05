package rpi.teacher

import rpi.{Names, Settings}
import rpi.inference._
import rpi.util.Namespace
import viper.silver.ast.SimpleInfo
import viper.silver.{ast => sil}

import scala.annotation.tailrec
import scala.collection.mutable

/**
  * Builds programs used to check hypotheses.
  *
  * @param teacher The pointer to the teacher.
  */
class CheckBuilder(teacher: Teacher) {
  // import utility methods

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
  private def original: sil.Program = inference.labeled

  /**
    * The namespace used to generate unique identifiers.
    */
  private var namespace: Namespace = _

  /**
    * The context information for the example extractor.
    */
  private var context: Context = _

  /**
    * The stack of statement buffers used to accumulate the instrumented statements. The stack is required to properly
    * handle control flow. The topmost buffer accumulates statements for the current branch.
    */
  private var stack: List[mutable.Buffer[sil.Stmt]] = _

  /**
    * Returns a program that performs self-framing checks for the given hypothesis.
    *
    * @param hypothesis The hypothesis to check for self-framingness.
    * @return The program and the context object.
    */
  def framingCheck(hypothesis: Hypothesis): (sil.Program, Context) = {
    /**
      * Helper method that inhales the conjuncts of the given expression.
      *
      * @param expression The expression to inhale.
      */
    def addInhales(expression: sil.Exp): Unit =
      expression match {
        case sil.And(left, right) =>
          addInhales(left)
          addInhales(right)
        case conjunct =>
          // create context information
          val info = getLocation(conjunct)
            .map { location => FramingInfo(location) }
            .getOrElse(sil.NoInfo)
          // inhale conjunct
          val inhale = sil.Inhale(conjunct)(info = info)
          addStatement(inhale)
      }

    /**
      * Helper method that extracts the location from the given expression.
      *
      * This method assumes that there is at most one location access that is potentially guarded by some conditions.
      *
      * @param expression The expression.
      * @return The extracted location access.
      */
    @tailrec
    def getLocation(expression: sil.Exp): Option[sil.LocationAccess] =
      expression match {
        case sil.TrueLit() => None
        case sil.FalseLit() => None
        case sil.FieldAccessPredicate(location, _) => Some(location)
        case sil.PredicateAccessPredicate(location, _) => Some(location)
        case sil.Implies(_, guarded) => getLocation(guarded)
        case _ => ???
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
        context.addInhaled(label, instance)
        // inhale inferred specification
        val inferred = hypothesis.get(instance)
        addInhales(inferred)
        // return check
        asSequence(pop())
      }
      .toSeq

    // return program
    val dummy = Hypothesis(Map.empty)
    val program = buildProgram(checks, dummy)
    (program, context)
  }

  /**
    * Returns a program that performs the given checks.
    *
    * @param checks     The checks to perform.
    * @param hypothesis The hypothesis.
    * @return The program and the context object.
    */
  def basicCheck(checks: Seq[sil.Seqn], hypothesis: Hypothesis): (sil.Program, Context) = {
    import Names._

    // remember the last inhaled specification (to be handled by future unfold annotations)
    // and the last fold annotation (to be handled by future exhaled specifications)
    var inhaled: Option[sil.Exp] = None
    var annotation: Option[sil.MethodCall] = None

    /**
      * Helper method that instruments the given sequence.
      *
      * @param sequence The sequence to instrument.
      * @return The instrumented sequence.
      */
    def instrumentSequence(sequence: sil.Seqn): sil.Seqn = {
      push()
      sequence.ss.foreach { statement => instrumentStatement(statement) }
      asSequence(pop())
    }

    /**
      * Helper method that instruments the given statement.
      *
      * @param statement The statement to instrument.
      */
    def instrumentStatement(statement: sil.Stmt): Unit =
      statement match {
        case sil.If(condition, thenBody, elseBody) =>
          // instrument branches
          val thenInstrumented = instrumentSequence(thenBody)
          val elseInstrumented = instrumentSequence(elseBody)
          // add instrumented conditional
          val instrumented = sil.If(condition, thenInstrumented, elseInstrumented)()
          addStatement(instrumented)
        case sil.Inhale(predicate: sil.PredicateAccessPredicate) =>
          // get specification
          val instance = getInstance(predicate)
          val body = hypothesis.get(instance)
          inhaled = Some(body)
          // inhale
          if (Settings.inline) {
            // inhale body of specification predicate
            val info = SimpleInfo(Seq(instance.name))
            addStatement(sil.Inhale(body)(info = info))
          } else {
            // inhale and unfold specification predicate
            val adapted = {
              val name = instance.name
              val arguments = instance.arguments
              val access = sil.PredicateAccess(arguments, name)()
              sil.PredicateAccessPredicate(access, predicate.perm)()
            }
            addStatement(sil.Inhale(adapted)())
            addStatement(sil.Unfold(adapted)())
          }
          // save state
          val label = saveState(instance)
          context.addInhaled(label, instance)
        case sil.Exhale(predicate: sil.PredicateAccessPredicate) =>
          // get specification
          val instance = getInstance(predicate)
          val body = hypothesis.get(instance)
          // save state
          val label = saveState(instance)
          context.addExhaled(label, instance)
          // save and fold ingredients
          if (Settings.useAnnotations) {
            annotation match {
              case Some(sil.MethodCall(`foldUpAnnotation`, Seq(argument), _)) =>
                foldUp(body)(argument, label)
                annotation = None
              case None => save(body)(label)
            }
          } else foldAll(body)(label)
          // exhale
          val info = BasicInfo(label, instance)
          if (Settings.inline) {
            // exhale body of specification
            addStatement(sil.Exhale(body)(info = info))
          } else {
            // fold and exhale specification predicate
            val adapted = {
              val name = instance.name
              val arguments = instance.arguments
              val access = sil.PredicateAccess(arguments, name)()
              sil.PredicateAccessPredicate(access, predicate.perm)()
            }
            addStatement(sil.Fold(adapted)(info = info))
            addStatement(sil.Exhale(adapted)())
          }
        case call@sil.MethodCall(name, Seq(argument), _) if Names.isAnnotation(name) =>
          // handle annotations (only occur when enabled)
          name match {
            case `unfoldDownAnnotation` =>
              inhaled.foreach { expression => unfoldDown(expression)(argument) }
              inhaled = None
            case `foldUpAnnotation` =>
              annotation = Some(call)
          }
        case _ =>
          addStatement(statement)
      }

    def unfoldDown(expression: sil.Exp, guards: Seq[sil.Exp] = Seq.empty)
                  (implicit argument: sil.Exp): Unit =
      expression match {
        case sil.And(left, right) =>
          unfoldDown(left, guards)
          unfoldDown(right, guards)
        case sil.Implies(guard, guarded) =>
          unfoldDown(guarded, guards :+ guard)
        case predicate@sil.PredicateAccessPredicate(sil.PredicateAccess(arguments, _), _) =>
          val unfold = sil.Unfold(predicate)()
          val conditions = guards :+ sil.EqCmp(argument, arguments.head)()
          val conditional = sil.If(bigAnd(conditions), asSequence(unfold), skip)()
          addStatement(conditional)
        case _ => // do nothing
      }

    def save(expression: sil.Exp)(implicit label: String): Unit =
      expression match {
        case sil.And(left, right) =>
          save(left)
          save(right)
        case sil.Implies(_, guarded) =>
          save(guarded)
        case sil.FieldAccessPredicate(resource, _) =>
          savePermission(label, resource)
        case sil.PredicateAccessPredicate(resource, _) =>
          savePermission(label, resource)
        case _ => // do nothing
      }

    def foldUp(expression: sil.Exp, guards: Seq[sil.Exp] = Seq.empty)
              (implicit argument: sil.Exp, label: String): Unit =
      expression match {
        case sil.And(left, right) =>
          foldUp(left, guards)
          foldUp(right, guards)
        case sil.Implies(guard, guarded) =>
          foldUp(guarded, guards :+ guard)
        case predicate@sil.PredicateAccessPredicate(sil.PredicateAccess(arguments, name), _) =>
          // save body
          val instance = inference.getInstance(name, arguments)
          val body = hypothesis.get(instance)
          save(body)
          // conditional fold
          val info = BasicInfo(label, instance)
          val fold = sil.Fold(predicate)(info = info)
          val conditions = guards :+ sil.EqCmp(argument, arguments.head)()
          addStatement(sil.If(bigAnd(conditions), asSequence(fold), skip)())
        case other => save(other)
      }

    def foldAll(expression: sil.Exp, guards: Seq[sil.Exp] = Seq.empty, depth: Int = 0)
               (implicit label: String): Unit =
      expression match {
        case sil.And(left, right) =>
          foldAll(left, guards, depth)
          foldAll(right, guards, depth)
        case sil.Implies(guard, guarded) =>
          foldAll(guarded, guards :+ guard, depth)
        case predicate@sil.PredicateAccessPredicate(sil.PredicateAccess(arguments, name), _) if depth < Settings.foldDepth =>
          // recursively fold body
          val instance = inference.getInstance(name, arguments)
          val body = hypothesis.get(instance)
          foldAll(body, guards, depth + 1)
          // conditional fold
          val info = BasicInfo(label, instance)
          val fold = sil.Fold(predicate)(info = info)
          addStatement(sil.If(bigAnd(guards), asSequence(fold), skip)())
        case other => save(other)
      }

    // build instrumented program
    clear()
    val instrumented = checks.map { check => instrumentSequence(check) }
    val program = buildProgram(instrumented, hypothesis)
    // return program and context
    (program, context)
  }

  /**
    * Builds a program with the given checks. Most components are taken over from the original  program.
    *
    * @param checks     The checks.
    * @param hypothesis The hypothesis.
    * @return The program.
    */
  private def buildProgram(checks: Seq[sil.Seqn], hypothesis: Hypothesis): sil.Program = {
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
    val methods = checks.map { check => buildMethod(check) }
    val extensions = Seq.empty
    val program = sil.Program(domains, fields, functions, predicates, methods, extensions)()
    println(program)
    program
  }

  /**
    * Builds a method performing to the given check.
    *
    * @param check The check.
    * @return The method.
    */
  private def buildMethod(check: sil.Seqn): sil.Method = {
    val name = namespace.uniqueIdentifier(base = "check", Some(0))
    val arguments = Seq.empty
    val returns = Seq.empty
    val preconditions = Seq.empty
    val postconditions = Seq.empty
    val body = {
      val statements = check.ss
      val declarations = check
        .deepCollect { case variable: sil.LocalVar => variable }
        .distinct
        .map { variable => sil.LocalVarDecl(variable.name, variable.typ)() }
      Some(sil.Seqn(statements, declarations)())
    }
    sil.Method(name, arguments, returns, preconditions, postconditions, body)()
  }

  private def getInstance(predicate: sil.PredicateAccessPredicate): Instance = {
    // make sure all arguments are variable accesses
    val access = predicate.loc
    val (arguments, assignments) = {
      val empty = (Seq.empty[sil.LocalVar], Seq.empty[sil.LocalVarAssign])
      access.args.foldLeft(empty) {
        case ((variables, collected), variable: sil.LocalVar) =>
          (variables :+ variable, collected)
        case ((variables, collected), argument) =>
          val name = namespace.uniqueIdentifier(base = "t", Some(0))
          val variable = sil.LocalVar(name, argument.typ)()
          val assignment = sil.LocalVarAssign(variable, argument)()
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
        case variable: sil.LocalVar =>
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
          saveValue(name, atom)
      }
    // add label
    addStatement(sil.Label(label, Seq.empty)())
    label
  }

  /**
    * Saves the currently held permission amount for the given resource.
    *
    * @param label    The label of the state under which the name of the variable should be stored.
    * @param resource The resource.
    */
  private def savePermission(label: String, resource: sil.LocationAccess): Unit = {
    // auxiliary method to extract condition under which we have permission to even talk about this resource
    def extractConditions(resource: sil.Exp): Seq[sil.Exp] =
      resource match {
        case access: sil.FieldAccess =>
          val name = context.getName(label, access)
          val variable = sil.LocalVar(name, sil.Perm)()
          Seq(sil.PermGtCmp(variable, sil.NoPerm()())())
        case _ => Seq.empty
      }

    // auxiliary method to actually save the permission
    def savePermission(conditions: Seq[sil.Exp]): Unit = {
      // generate unique name
      val name = namespace.uniqueIdentifier(base = "p", Some(0))
      context.addName(label, resource, name)
      // construct potentially conditional value
      val value = {
        val current = sil.CurrentPerm(resource)()
        if (conditions.isEmpty) current
        else sil.CondExp(bigAnd(conditions), current, sil.NoPerm()())()
      }
      // save value
      saveValue(name, value)
    }

    // process resource
    resource match {
      case sil.FieldAccess(receiver, _) =>
        val conditions = extractConditions(receiver)
        savePermission(conditions)
      case sil.PredicateAccess(arguments, _) =>
        val conditions = arguments.flatMap { argument => extractConditions(argument) }
        savePermission(conditions)
    }
  }

  /**
    * Saves the value of the given expression in a variable with the given name.
    *
    * @param name       The name of the variable.
    * @param expression The expression to save.
    */
  private def saveValue(name: String, expression: sil.Exp): Unit = {
    val variable = sil.LocalVar(name, expression.typ)()
    if (Settings.useBranching && expression.typ == sil.Bool) {
      // create conditional
      val thenBody = asSequence(sil.LocalVarAssign(variable, sil.TrueLit()())())
      val elseBody = asSequence(sil.LocalVarAssign(variable, sil.FalseLit()())())
      addStatement(sil.If(expression, thenBody, elseBody)())
    } else {
      // create assignment
      addStatement(sil.LocalVarAssign(variable, expression)())
    }
  }

  private def addStatement(statement: sil.Stmt): Unit =
    stack.head.append(statement)

  private def clear(): Unit = {
    namespace = new Namespace
    context = new Context
    stack = List.empty
  }

  private def push(): Unit =
    stack = mutable.Buffer.empty[sil.Stmt] :: stack

  private def pop(): Seq[sil.Stmt] =
    stack match {
      case head :: tail =>
        stack = tail
        head.toSeq
    }
}