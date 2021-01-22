package rpi.teacher

import rpi.Names
import rpi.inference._
import rpi.builder.{Folding, ProgramBuilder}
import rpi.util.Expressions._
import rpi.util.Namespace
import rpi.util.Statements._
import viper.silver.ast

/**
  * Builds programs used to check hypotheses.
  *
  * @param teacher The pointer to the teacher.
  */
class CheckBuilder(teacher: Teacher) extends ProgramBuilder(teacher.context) with Folding {

  private def configuration = context.configuration

  /**
    * The flag indicating whether the use of annotations is enabled.
    */
  private val useAnnotations: Boolean = configuration.useAnnotations()

  /**
    * The depth up to which predicates are statically folded when the heuristics is enabled.
    */
  private val heuristicsFoldDepth: Int = configuration.heuristicsFoldDepth()

  /**
    * The flag indicating whether specification inlining is disabled.
    */
  private val noInlining: Boolean = configuration.noInlining()

  /**
    * The flag indicating whether branching on atomic predicates is disabled.
    */
  private val noBranching: Boolean = configuration.noBranching()

  /**
    * Returns the pointer to the original program (labeled).
    *
    * @return The pointer to the original program.
    */
  private def original: ast.Program = context.labeled

  /**
    * The namespace used to generate unique identifiers.
    */
  private var namespace: Namespace = _

  /**
    * The context information for the sample extractor.
    */
  private var checkContext: CheckContext = _

  /**
    * Returns a program that performs self-framing checks for the given hypothesis.
    *
    * @param hypothesis The hypothesis to check for self-framingness.
    * @return The program and the context object.
    */
  def framingChecks(hypothesis: Hypothesis): (ast.Program, CheckContext) = {
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
          val condition = makeImplication(makeAnd(guards), conjunct)
          addInhale(condition, info)
      }

    // create a check for each specification predicate
    clear()
    val checks = hypothesis
      .predicates
      .map { predicate =>
        makeScope {
          // save state snapshot
          val arguments = predicate.formalArgs.map { parameter => parameter.localVar }
          val instance = context.getInstance(predicate.name, arguments)
          val label = saveSnapshot(instance)
          checkContext.addSnapshot(label, instance)
          // inhale inferred specification
          val inferred = hypothesis.getPredicateBody(instance)
          addInhales(inferred)
          // return check
        }
      }

    // return program
    val dummy = Hypothesis(Seq.empty, Seq.empty)
    val program = buildProgram(checks, dummy)
    (program, checkContext)
  }

  /**
    * Returns a program that performs the given checks.
    * @param checks     The checks.
    * @param hypothesis The hypothesis.
    * @return The program and the context object.
    */
  def basicChecks(checks: Seq[Check], hypothesis: Hypothesis): (ast.Program, CheckContext) = {
    // instrument checks
    clear()
    val instrumented = checks.map { check => basicCheck(check, hypothesis) }
    // return program and context
    val program = buildProgram(instrumented, hypothesis)
    (program, checkContext)
  }

  /**
    * Returns the body of a method performing the given check.
    * @param check      The check.
    * @param hypothesis The hypothesis.
    * @return The body.
    */
  private def basicCheck(check: Check, hypothesis: Hypothesis): ast.Seqn = {
    import Names._

    // compute unfold and fold depth
    val (unfoldDepth, foldDepth) =
      if (useAnnotations) {
        val baseDepth = check.baseDepth(hypothesis)
        (baseDepth, baseDepth)
      } else (0, heuristicsFoldDepth)

    /**
      * Helper method that instruments the given sequence.
      *
      * @param sequence The sequence to instrument.
      * @return The instrumented sequence.
      */
    def instrumentSequence(sequence: ast.Seqn): ast.Seqn =
      makeScope {
        sequence
          .ss
          .foreach { statement => instrumentStatement(statement) }
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
          addConditional(condition, thenInstrumented, elseInstrumented)
        case ast.Inhale(expression) => expression match {
          case condition if condition.isPure =>
            // inhale pure conditions (presumably non-specification)
            addInhale(condition)
          case predicate: ast.PredicateAccessPredicate =>
            // get specification
            val instance = getInstance(predicate)
            val body = hypothesis.getPredicateBody(instance)
            // inhale predicate
            if (noInlining) {
              // inhale and unfold specification predicate
              val adapted = {
                val name = instance.name
                val arguments = instance.arguments
                val access = ast.PredicateAccess(arguments, name)()
                ast.PredicateAccessPredicate(access, predicate.perm)()
              }
              addInhale(adapted)
              addUnfold(adapted)
            } else {
              // inhale body of specification predicate
              val info = ast.SimpleInfo(Seq(instance.toString))
              addInhale(body, info)
            }
            // unfold predicate
            unfold(body)(unfoldDepth, hypothesis)
            // save state snapshot
            val label = saveSnapshot(instance)
            checkContext.addSnapshot(label, instance)
            old = Some(label)
        }
        case ast.Exhale(expression) => expression match {
          case condition if condition.isPure =>
            // exhale pure conditions (presumably non-specification)
            addExhale(condition)
          case predicate: ast.PredicateAccessPredicate =>
            // get specification
            val instance = getInstance(predicate)
            val body = hypothesis.getPredicateBody(instance)
            // save state snapshot
            implicit val label: String = saveSnapshot(instance)
            checkContext.addSnapshot(label, instance)
            // save ingredients and fold predicate
            if (useAnnotations) {
              val annotations: Seq[Annotation] = Annotations.extract(statement)
              foldWithAnnotations(body, annotations)(foldDepth, hypothesis, savePermission)
            } else fold(body)(foldDepth, hypothesis, savePermission)
            // exhale predicate
            val info = BasicInfo(instance)
            if (noInlining) {
              // fold and exhale specification predicate
              val adapted = {
                val name = instance.name
                val arguments = instance.arguments
                val access = ast.PredicateAccess(arguments, name)()
                ast.PredicateAccessPredicate(access, predicate.perm)()
              }
              addFold(adapted, info)
              addExhale(adapted)
            } else {
              // exhale body of specification
              addExhale(body, info)
            }
        }
        case call@ast.MethodCall(name, _, _) if Names.isAnnotation(name) =>
          sys.error(s"Unhandled annotation: $call")
        case _ =>
          addStatement(statement)
      }

    // instrument check
    val sequence = makeSequence(check.statements)
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
      if (useAnnotations) original.fields
      else context.inference.magic +: original.fields
    val functions = original.functions
    val predicates = {
      val existing = original.predicates
      val inferred = context.predicates(hypothesis)
      existing ++ inferred
    }
    val methods = {
      val lemmaMethods = hypothesis.lemmas
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
      Some(makeSequence(statements, declarations))
    }
    ast.Method(name, arguments, returns, preconditions, postconditions, body)()
  }

  private def getInstance(predicate: ast.PredicateAccessPredicate): Instance = {
    // TODO: Do when checks are created.
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

    assignments.foreach { assignment => addStatement(assignment) }

    // create and return instance
    val name = access.predicateName
    context.getInstance(name, arguments)
  }

  /**
    * Saves a state snapshot for the given specification instance.
    *
    * @param instance The instance.
    * @return The label of the state snapshot.
    */
  private def saveSnapshot(instance: Instance): String = {
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

  private def savePermission(expression: ast.Exp, guards: Seq[ast.Exp])(implicit label: String): Unit =
    expression match {
      case ast.FieldAccessPredicate(resource, _) => savePermission(resource, guards)
      case ast.PredicateAccessPredicate(resource, _) => savePermission(resource, guards)
      case _ => // do nothing
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
          val name = checkContext.getName(label, access)
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
    checkContext.addName(label, resource, name)
    // construct potentially conditional value
    val value = {
      val current = ast.CurrentPerm(resource)()
      if (conditions.isEmpty) current
      else ast.CondExp(makeAnd(conditions), current, ast.NoPerm()())()
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
    if (noBranching) saveValue(name, atom)
    else {
      // create variable
      val variable = ast.LocalVar(name, ast.Bool)()
      // create conditional
      val thenBody = makeAssign(variable, makeTrue)
      val elseBody = makeAssign(variable, makeFalse)
      addConditional(atom, thenBody, elseBody)
    }


  /**
    * Saves the value of the given expression in a variable with the given name.
    *
    * @param name       The name of the variable.
    * @param expression The expression to save.
    */
  private def saveValue(name: String, expression: ast.Exp): Unit = {
    // create variable and assignment
    val variable = ast.LocalVar(name, expression.typ)()
    addAssign(variable, expression)
  }

  private def clear(): Unit = {
    namespace = new Namespace
    checkContext = new CheckContext(configuration)
  }
}