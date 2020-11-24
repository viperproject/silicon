package rpi.teacher

import rpi.Config
import rpi.inference._
import rpi.util.Namespace
import viper.silver.ast.{NoInfo, SimpleInfo}
import viper.silver.{ast => sil}

/**
  * Builds programs used to check hypothesis.
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

  private def base: sil.Program = inference.labeled

  private var namespace: Namespace = _

  /**
    * The accumulated statements.
    */
  private var statements: Seq[sil.Stmt] = _

  private var predicates: Seq[sil.Predicate] = _

  private var context: Context = _

  /**
    * Returns a program that performs a check.
    *
    * @param check      The check to perform.
    * @param hypothesis The hypothesis.
    * @return The program.
    */
  def basicCheck(check: Check, hypothesis: Hypothesis): (sil.Program, Context) = {
    // reset
    reset()
    // add predicates
    inference
      .predicates(hypothesis)
      .foreach(addPredicate)
    // add statements and instrumentation
    check
      .statements
      .foreach {
        case sil.Inhale(predicate: sil.PredicateAccessPredicate) =>
          // inhale specification
          addInhale(predicate)
          addUnfold(predicate)
          // save state
          val instance = inference.instance(predicate.loc)
          saveState(instance)
        case sil.Exhale(predicate: sil.PredicateAccessPredicate) =>
          // save permissions
          val instance = inference.instance(predicate.loc)
          savePermissions(instance, hypothesis)
          // save state
          val label = saveState(instance)
          // exhale specification
          addFold(predicate, Some(label))
          addExhale(predicate)
        case statement => addStatement(statement)
      }
    // return program and states
    (buildProgram(), context)
  }

  /**
    * Returns a program that performs a check whether the specification referred to by the given instance is
    * self-framing.
    *
    * @param instance   The instance.
    * @param hypothesis The hypothesis containing the actual specification.
    * @return The program.
    */
  def framingCheck(instance: Instance, hypothesis: Hypothesis): sil.Program = {
    // reset
    reset()
    // save state
    saveState(instance, useActuals = false)
    // inhale hypothesis
    val name = instance.name
    addInhale(hypothesis.get(name))
    // return program
    buildProgram()
  }

  /**
    * Resets the check builder.
    */
  private def reset(): Unit = {
    // TODO: Copy namespace from labeled program.
    namespace = new Namespace
    statements = Seq.empty
    predicates = Seq.empty
    context = new Context
  }

  /**
    * Adds the given statement.
    *
    * @param statement The statement to add.
    */
  private def addStatement(statement: sil.Stmt): Unit =
    statements = statements :+ statement

  /**
    * Adds a statement that inhales the given expression.
    *
    * @param expression The expression to inhale.
    */
  private def addInhale(expression: sil.Exp): Unit = {
    val inhale = sil.Inhale(expression)()
    addStatement(inhale)
  }

  /**
    * Adds a statement that exhales the given expression.
    *
    * @param expression The expression to exhale.
    */
  private def addExhale(expression: sil.Exp): Unit = {
    val exhale = sil.Exhale(expression)()
    addStatement(exhale)
  }

  /**
    * Adds a statement that folds the given predicate.
    *
    * @param predicate The predicate to fold.
    */
  private def addFold(predicate: sil.PredicateAccessPredicate, label: Option[String] = None): Unit = {
    val info = label
      .map { name => SimpleInfo(Seq(name)) }
      .getOrElse(NoInfo)
    val fold = sil.Fold(predicate)(info = info)
    addStatement(fold)
  }

  /**
    * Adds a statement that unfolds the given predicate.
    *
    * @param predicate The predicate to unfold.
    */
  private def addUnfold(predicate: sil.PredicateAccessPredicate): Unit = {
    val unfold = sil.Unfold(predicate)()
    addStatement(unfold)
  }

  /**
    * Adds a label with the given name.
    *
    * @param name The name of the label.
    */
  private def addLabel(name: String): Unit = {
    val label = sil.Label(name, Seq.empty)()
    addStatement(label)
  }

  private def saveState(instance: Instance, useActuals: Boolean = true): String = {
    val label = namespace.uniqueIdentifier(base = "s", Some(0))
    context.addInstance(label, instance)
    // save values of all variables
    instance
      .arguments
      .foreach { variable =>
        val name = s"${label}_${variable.name}"
        saveValue(name, variable)
      }
    // save values of all atoms
    val atoms =
      if (useActuals) instance.actualAtoms
      else instance.formalAtoms
    atoms
      .zipWithIndex
      .foreach { case (atom, index) =>
        val name = s"${label}_$index"
        saveValue(name, atom)
      }
    // label state and return name of label
    addLabel(label)
    label
  }

  private def savePermissions(instance: Instance, hypothesis: Hypothesis): Unit =
    hypothesis
      .get(instance.name)
      .collect {
        case sil.FieldAccessPredicate(access, _) => access
        case sil.PredicateAccessPredicate(access, _) => access
      }
      .foreach { access =>
        val adapted = instance.toActual(access)
        val name = namespace.uniqueIdentifier(base = "p", Some(0))
        context.addVariable(adapted, name)
        savePermission(name, adapted)
      }

  /**
    * Saves the currently held permissions for the given resource using a variable with the given name.
    *
    * @param name     The name of the variable.
    * @param resource The resource.
    */
  private def savePermission(name: String, resource: sil.ResourceAccess): Unit = {
    val value = sil.CurrentPerm(resource)()
    saveValue(name, value)
  }

  /**
    * Saves the value of the given expression using a variable with the given name.
    *
    * @param name       The name of the variable.
    * @param expression The expression to save.
    */
  private def saveValue(name: String, expression: sil.Exp): Unit = {
    val variable = sil.LocalVar(name, expression.typ)()
    if (Config.useBranching && expression.typ == sil.Bool) {
      // build then branch assigning true
      val thenBody = {
        val assignment = sil.LocalVarAssign(variable, sil.TrueLit()())()
        sil.Seqn(Seq(assignment), Seq.empty)()
      }
      // build else branch assigning false
      val elseBody = {
        val assignment = sil.LocalVarAssign(variable, sil.FalseLit()())()
        sil.Seqn(Seq(assignment), Seq.empty)()
      }
      // build and add conditional
      val conditional = sil.If(expression, thenBody, elseBody)()
      addStatement(conditional)
    } else {
      // build and add assignment
      val assignment = sil.LocalVarAssign(variable, expression)()
      addStatement(assignment)
    }
  }

  private def addPredicate(predicate: sil.Predicate): Unit =
    predicates = predicates :+ predicate

  /**
    * Builds and returns the body of the check method.
    *
    * @return The body.
    */
  private def buildBody(): sil.Seqn = {
    // compute declarations from statements
    val declarations = statements
      .flatMap { statement =>
        statement.deepCollect { case variable: sil.LocalVar => variable }
      }
      .distinct
      .map { variable => sil.LocalVarDecl(variable.name, variable.typ)() }
    // create body
    sil.Seqn(statements, declarations)()
  }

  /**
    * Builds and returns the check method.
    *
    * @return The check method.
    */
  private def buildMethod(): sil.Method = {
    val name = "check"
    val arguments = Seq.empty
    val returns = Seq.empty
    val preconditions = Seq.empty
    val postconditions = Seq.empty
    val body = Some(buildBody())
    sil.Method(name, arguments, returns, preconditions, postconditions, body)()
  }

  /**
    * Builds and returns a program with the check method.
    *
    * @return The program.
    */
  private def buildProgram(): sil.Program = {
    val domains = Seq.empty
    val fields =
      if (Config.useHeuristics) {
        // add magic fields that enables fold / unfold heuristics
        val magic = sil.Field("__CONFIG_HEURISTICS", sil.Bool)()
        magic +: base.fields
      } else base.fields
    val functions = Seq.empty
    val methods = Seq(buildMethod())
    val extensions = Seq.empty
    sil.Program(domains, fields, functions, predicates, methods, extensions)()
  }
}
