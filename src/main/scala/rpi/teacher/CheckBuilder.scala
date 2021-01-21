package rpi.teacher

import rpi.{Names, Settings}
import rpi.inference._
import rpi.util.Expressions._
import rpi.util.Namespace
import rpi.util.Statements._
import viper.silver.ast

import scala.collection.mutable
import scala.collection.mutable.ListBuffer

/**
  * Builds programs used to check hypotheses.
  *
  * @param teacher The pointer to the teacher.
  */
class CheckBuilder(teacher: Teacher) {


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
    * The buffer used to accumulate statements for the current scope.
    */
  private var buffer: mutable.Buffer[ast.Stmt] = _

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
          val instance = inference.getInstance(predicate.name, arguments)
          val label = saveSnapshot(instance)
          context.addSnapshot(label, instance)
          // inhale inferred specification
          val inferred = hypothesis.getPredicateBody(instance)
          addInhales(inferred)
          // return check
        }
      }

    // return program
    val dummy = Hypothesis(Seq.empty, Seq.empty)
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

    // compute unfold and fold depth
    val unfoldDepth: Int = check.baseDepth(hypothesis)
    val foldDepth: Int = unfoldDepth + Settings.foldDelta

    // TODO: Incorporate into annotation info.
    var old: Option[String] = None

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
            if (Settings.inline) {
              // inhale body of specification predicate
              val info = ast.SimpleInfo(Seq(instance.toString))
              addInhale(body, info)
            } else {
              // inhale and unfold specification predicate
              val adapted = {
                val name = instance.name
                val arguments = instance.arguments
                val access = ast.PredicateAccess(arguments, name)()
                ast.PredicateAccessPredicate(access, predicate.perm)()
              }
              addInhale(adapted)
              addUnfold(adapted)
            }
            // unfold predicate
            unfold(body)(unfoldDepth)
            // save state snapshot
            val label = saveSnapshot(instance)
            context.addSnapshot(label, instance)
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
            context.addSnapshot(label, instance)
            // save ingredients and fold predicate
            val annotations: Seq[Annotation] = Annotations.extract(statement)
            if (annotations.nonEmpty) handleAnnotations(body, annotations)(foldDepth, label)
            else saveAndFold(body)(foldDepth, label)
            // exhale predicate
            val info = BasicInfo(label, instance)
            if (Settings.inline) {
              // exhale body of specification
              addExhale(body, info)
            } else {
              // fold and exhale specification predicate
              val adapted = {
                val name = instance.name
                val arguments = instance.arguments
                val access = ast.PredicateAccess(arguments, name)()
                ast.PredicateAccessPredicate(access, predicate.perm)()
              }
              addFold(adapted, info)
              addExhale(adapted)
            }
        }
        case call@ast.MethodCall(name, _, _) if Names.isAnnotation(name) =>
          sys.error(s"Unhandled annotation: $call")
        case _ =>
          addStatement(statement)
      }

    /**
      * Recursively unfolds predicates appearing in the given expression.
      *
      * @param expression The expression to unfold.
      * @param guards     The guards collected so far.
      * @param maxDepth   The implicitly passed maximal depth up to which to unfold.
      */
    def unfold(expression: ast.Exp, guards: Seq[ast.Exp] = Seq.empty)
              (implicit maxDepth: Int): Unit =
      expression match {
        case ast.And(left, right) =>
          unfold(left, guards)
          unfold(right, guards)
        case ast.Implies(guard, guarded) =>
          unfold(guarded, guards :+ guard)
        case predicate@ast.PredicateAccessPredicate(ast.PredicateAccess(arguments, name), _) =>
          val depth = getDepth(arguments.head)
          if (depth <= maxDepth) {
            val unfolds = makeScope {
              // unfold predicate
              addUnfold(predicate)
              // recursively unfold predicates appearing in body
              if (depth < maxDepth) {
                val instance = inference.getInstance(name, arguments)
                val body = hypothesis.getPredicateBody(instance)
                unfold(body)
              }
            }
            addConditional(guards, unfolds)
          }
        case _ => // do nothing
      }

    /**
      * Recursively folds predicates appearing in the given expression. Moreover, this method also saves permission
      * amounts held for all of the ingredients.
      *
      * @param expression  The expression to fold.
      * @param guards      The guards collected so far.
      * @param maxDepth    The implicitly passed maximal depth up to which to fold.
      * @param label       The implicitly passed label of the current state snapshot.
      */
    def saveAndFold(expression: ast.Exp, guards: Seq[ast.Exp] = Seq.empty)
                   (implicit maxDepth: Int, label: String): Unit =
      expression match {
        case ast.And(left, right) =>
          saveAndFold(left, guards)
          saveAndFold(right, guards)
        case ast.Implies(guard, guarded) =>
          saveAndFold(guarded, guards :+ guard)
        case ast.FieldAccessPredicate(resource, _) =>
          savePermission(resource, guards)
        case predicate@ast.PredicateAccessPredicate(resource@ast.PredicateAccess(arguments, name), _) =>
          val depth = getDepth(arguments.head)
          if (depth <= maxDepth) {
            val folds = makeScope {
              // recursively fold predicates appearing in body
              val instance = inference.getInstance(name, arguments)
              val body = hypothesis.getPredicateBody(instance)
              saveAndFold(body)
              // fold predicate
              val info = BasicInfo(label, instance)
              addFold(predicate, info)
            }
            addConditional(guards, folds)
          } else {
            savePermission(resource, guards)
          }
        case _ => // do nothing
      }

    /**
      * Handles the given annotations and then saves and folds the given expression.
      *
      * @param expression  The expression to fold.
      * @param annotations The annotations.
      * @param maxDepth    The implicitly passed maximal depth up to which to fold.
      * @param label       The implicitly passed label of the current state snapshot.
      */
    def handleAnnotations(expression: ast.Exp, annotations: Seq[Annotation])
                         (implicit maxDepth: Int, label: String): Unit = {
      /**
        * Handles the end argument of predicate instances (and afterwards, handles the start argument of predicate
        * instances, and finally saves and folds the expression).
        *
        * @param expression The expression to handle.
        * @param guards     The guards collected so far.
        */
      def handleEnd(expression: ast.Exp, guards: Seq[ast.Exp] = Seq.empty): Unit =
        expression match {
          case ast.And(left, right) =>
            handleEnd(left, guards)
            handleEnd(right, guards)
          case ast.Implies(guard, guarded) =>
            handleEnd(guarded, guards :+ guard)
          case predicate: ast.PredicateAccessPredicate =>
            val arguments = predicate.loc.args
            arguments match {
              case Seq(start, end: ast.LocalVar) =>
                val body = makeScope {
                  // down condition
                  val condition = {
                    val equalities = annotations.map {
                      case Annotation(`downAnnotation`, argument) =>
                        makeEquality(end, argument)
                    }
                    makeOr(equalities)
                  }
                  // TODO:
                  val thenBody = makeScope {
                    // get lemma instance
                    val instance = {
                      val previous = ast.LocalVar(s"${old.get}_${end.name}", ast.Ref)()
                      val arguments = Seq(start, previous, end)
                      inference.getInstance(Names.appendLemma, arguments)
                    }
                    // fold lemma precondition
                    val precondition = hypothesis.getLemmaPrecondition(instance)
                    handleStart(precondition)
                    // apply lemma
                    val lemmaApplication = hypothesis.getLemmaApplication(instance)
                    addStatement(lemmaApplication)
                  }
                  val elseBody = makeScope(handleStart(predicate))
                  addConditional(condition, thenBody, elseBody)
                }
                addConditional(guards, body)
              case _ =>
                handleStart(predicate, guards)
            }
          case other =>
            saveAndFold(other, guards)
        }

      /**
        * Handles the start argument of predicates instances (and afterwards saves and folds the expression).
        *
        * @param expression The expression to handle.
        * @param guards     The guards collected so far.
        */
      def handleStart(expression: ast.Exp, guards: Seq[ast.Exp] = Seq.empty): Unit =
        expression match {
          case ast.And(left, right) =>
            handleStart(left, guards)
            handleStart(right, guards)
          case ast.Implies(guard, guarded) =>
            handleStart(guarded, guards :+ guard)
          case predicate: ast.PredicateAccessPredicate =>
            val body = makeScope {
              // down condition
              val condition = {
                val start = predicate.loc.args.head
                val equalities = annotations.map {
                  case Annotation(`downAnnotation`, argument) =>
                    makeEquality(start, argument)
                }
                makeOr(equalities)
              }
              // conditionally decrease the maximal fold depth
              val thenBranch = makeScope(saveAndFold(predicate)(maxDepth - 1, label))
              val elseBranch = makeScope(saveAndFold(predicate))
              addConditional(condition, thenBranch, elseBranch)
            }
            addConditional(guards, body)
          case other =>
            saveAndFold(other, guards)
        }

      // process expression
      handleEnd(expression)
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
      if (Settings.useAnnotations) original.fields
      else inference.magic +: original.fields
    val functions = original.functions
    val predicates = {
      val existing = original.predicates
      val inferred = inference.predicates(hypothesis)
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
    inference.getInstance(name, arguments)
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
    if (Settings.useBranching) {
      // create variable
      val variable = ast.LocalVar(name, ast.Bool)()
      // create conditional
      val thenBody = makeAssign(variable, makeTrue)
      val elseBody = makeAssign(variable, makeFalse)
      addConditional(atom, thenBody, elseBody)
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
    addAssign(variable, expression)
  }

  private def makeScope(generate: => Unit): ast.Seqn = {
    // save outer buffer and create and set current one
    val outer = buffer
    val current = ListBuffer.empty[ast.Stmt]
    buffer = current
    // generate inner statements
    generate
    // restore old buffer and return generated scope
    buffer = outer
    makeSequence(current.toSeq)
  }

  @inline
  private def addStatement(statement: ast.Stmt): Unit =
    buffer.append(statement)

  @inline
  private def addConditional(condition: ast.Exp, thenBody: ast.Stmt, elseBody: ast.Stmt): Unit =
    addStatement(makeConditional(condition, thenBody, elseBody))

  @inline
  private def addConditional(conditions: Seq[ast.Exp], thenBody: ast.Stmt): Unit =
    addConditional(conditions, thenBody, makeSkip)

  private def addConditional(conditions: Seq[ast.Exp], thenBody: ast.Stmt, elseBody: ast.Stmt): Unit =
    if (conditions.isEmpty) addStatement(thenBody)
    else addConditional(makeAnd(conditions), thenBody, elseBody)

  @inline
  private def addAssign(target: ast.LocalVar, value: ast.Exp): Unit =
    addStatement(makeAssign(target, value))

  @inline
  private def addInhale(expression: ast.Exp, info: ast.Info = ast.NoInfo): Unit =
    addStatement(ast.Inhale(expression)(info = info))

  @inline
  private def addExhale(expression: ast.Exp, info: ast.Info = ast.NoInfo): Unit =
    addStatement(ast.Exhale(expression)(info = info))

  @inline
  private def addUnfold(predicate: ast.PredicateAccessPredicate): Unit =
    addStatement(ast.Unfold(predicate)())

  @inline
  private def addFold(predicate: ast.PredicateAccessPredicate, info: ast.Info = ast.NoInfo): Unit =
    addStatement(ast.Fold(predicate)(info = info))


  private def clear(): Unit = {
    namespace = new Namespace
    context = new Context
  }
}