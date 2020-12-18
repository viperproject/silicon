package rpi.teacher

import rpi.Config
import rpi.inference._
import rpi.util.Namespace
import viper.silver.{ast => sil}

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
    clear()

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
    def getLocation(expression: sil.Exp): Option[sil.LocationAccess] =
      expression match {
        case sil.TrueLit() => None
        case sil.FalseLit() => None
        case sil.FieldAccessPredicate(location, _) => Some(location)
        case sil.PredicateAccessPredicate(location, _) => Some(location)
        case sil.Implies(_, guarded) => getLocation(guarded)
        case _ => ???
      }

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
    clear()
    val instrumented = checks.map { check => instrument(check, hypothesis) }
    // return program and context
    val program = buildProgram(instrumented, hypothesis)
    (program, context)
  }

  /**
    * Instruments the given sequence.
    *
    * @param sequence The sequence to instrument.
    * @return The instrumented sequence.
    */
  private def instrument(sequence: sil.Seqn, hypothesis: Hypothesis): sil.Seqn = {
    push()
    sequence.ss.foreach { statement => instrument(statement, hypothesis) }
    asSequence(pop())
  }

  /**
    * Instruments the given statement.
    *
    * @param statement The statement to instrument.
    */
  private def instrument(statement: sil.Stmt, hypothesis: Hypothesis): Unit =
    statement match {
      case sil.If(condition, thenBody, elseBody) =>
        // instrument branches
        val thenInstrumented = instrument(thenBody, hypothesis)
        val elseInstrumented = instrument(elseBody, hypothesis)
        // add instrumented conditional
        val instrumented = sil.If(condition, thenInstrumented, elseInstrumented)()
        addStatement(instrumented)
      case sil.Inhale(predicate: sil.PredicateAccessPredicate) =>
        // get specification instance
        val instance = getInstance(predicate)
        // inhale specification
        val adapted = adaptPredicate(predicate, instance, None)
        // TODO: Replace with inhale and unfold.
        addInhale(adapted)
        // save state
        val label = saveState(instance)
        context.addInhaled(label, instance)
      case sil.Exhale(predicate: sil.PredicateAccessPredicate) =>
        // get specification instance
        val instance = getInstance(predicate)
        // save state
        val label = saveState(instance)
        context.addExhaled(label, instance)
        // exhale specification
        foldAndExhale(instance, Seq.empty, depth = 0)(label, hypothesis)
      case sil.MethodCall(name, arguments, _) =>
        // TODO: Implement me.
        ???
      case _ =>
        addStatement(statement)
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
    val fields = inference.magic +: original.fields
    val functions = original.functions
    val predicates = {
      val existing = original.predicates
      val inferred = inference.predicates(hypothesis)
      existing ++ inferred
    }
    val methods = checks.map { check => buildMethod(check) }
    val extensions = Seq.empty
    sil.Program(domains, fields, functions, predicates, methods, extensions)()
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

  private def inhaleAndUnfold(instance: Instance, guards: Seq[sil.Exp], depth: Int)
                             (implicit hypothesis: Hypothesis): Unit = {
    // auxiliary method to recursively process nested instances
    def processNested(expression: sil.Exp, guards: Seq[sil.Exp]): Unit =
      expression match {
        case sil.And(left, right) =>
          processNested(left, guards)
          processNested(right, guards)
        case sil.Implies(left, right) =>
          processNested(right, guards :+ left)
        case sil.PredicateAccessPredicate(resource, _) =>
          if (depth < Config.foldDepth) {
            // TODO: Implement me
            val name = resource.predicateName
            val arguments = resource.args
            val inner = inference.getInstance(name, arguments)
            inhaleAndUnfold(inner, guards, depth + 1)
          }
        case _ => // do nothing
      }

    // create predicate
    val predicate = {
      val name = instance.name
      val arguments = instance.arguments
      val access = sil.PredicateAccess(arguments, name)()
      sil.PredicateAccessPredicate(access, sil.FullPerm()())()
    }

    // inhale top level instance
    if (depth == 0) addStatement(sil.Inhale(predicate)())

    // create conditional unfold statement
    val conditional = {
      val unfold = sil.Unfold(predicate)()
      if (guards.isEmpty) unfold
      else sil.If(bigAnd(guards), asSequence(unfold), skip)()
    }
    addStatement(conditional)

    // process nested instances
    val body = hypothesis.get(instance)
    processNested(body, guards)
  }

  private def foldAndExhale(instance: Instance, guards: Seq[sil.Exp], depth: Int)
                           (implicit label: String, hypothesis: Hypothesis): Unit = {
    // auxiliary method to recursively process nested instances
    def processNested(expression: sil.Exp, guards: Seq[sil.Exp]): Unit =
      expression match {
        case sil.TrueLit() => // do nothing
        case sil.And(left, right) =>
          processNested(left, guards)
          processNested(right, guards)
        case sil.Implies(left, right) =>
          processNested(right, guards :+ left)
        case sil.FieldAccessPredicate(resource, _) =>
          savePermission(label, resource)
        case sil.PredicateAccessPredicate(resource, _) =>
          if (depth < Config.foldDepth) {
            val name = resource.predicateName
            val arguments = resource.args
            val inner = inference.getInstance(name, arguments)
            foldAndExhale(inner, guards, depth + 1)
          } else savePermission(label, resource)
        case _ => ???
      }

    // process nested instances
    val body = hypothesis.get(instance)
    processNested(body, guards)

    // create predicate
    val predicate = {
      val name = instance.name
      val arguments = instance.arguments
      val access = sil.PredicateAccess(arguments, name)()
      sil.PredicateAccessPredicate(access, sil.FullPerm()())()
    }

    // create conditional fold statement
    val conditional = {
      val info = BasicInfo(label, instance)
      val fold = sil.Fold(predicate)(info = info)
      if (guards.isEmpty) fold
      else sil.If(bigAnd(guards), asSequence(fold), skip)()
    }
    addStatement(conditional)

    // exhale top level instance
    if (depth == 0) addStatement(sil.Exhale(predicate)())
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
    if (!Config.useFraming) ???
    assignments.foreach { assignment => addStatement(assignment) }

    // create and return instance
    val name = access.predicateName
    inference.getInstance(name, arguments)
  }

  private def adaptPredicate(predicate: sil.PredicateAccessPredicate, instance: Instance, label: Option[String]): sil.PredicateAccessPredicate = {
    val name = predicate.loc.predicateName
    val arguments = instance.arguments
    val access = sil.PredicateAccess(arguments, name)()
    val permission = predicate.perm
    val info = label.map { name => BasicInfo(name, instance) }.getOrElse(sil.NoInfo)
    sil.PredicateAccessPredicate(access, permission)(info = info)
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
    if (Config.useBranching && expression.typ == sil.Bool) {
      // create conditional
      val thenBody = asSequence(sil.LocalVarAssign(variable, sil.TrueLit()())())
      val elseBody = asSequence(sil.LocalVarAssign(variable, sil.FalseLit()())())
      addStatement(sil.If(expression, thenBody, elseBody)())
    } else {
      // create assignment
      addStatement(sil.LocalVarAssign(variable, expression)())
    }
  }

  private def addInhale(predicate: sil.PredicateAccessPredicate): Unit = {
    addStatement(sil.Inhale(predicate)())
    addStatement(sil.Unfold(predicate)())
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
        head
    }
}