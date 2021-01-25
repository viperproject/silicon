package rpi.teacher.query

import rpi.{Configuration, Names}
import rpi.builder.{CheckExtender, Folding}
import rpi.context.{Check, Context}
import rpi.inference.{Hypothesis, Instance}
import rpi.teacher.QueryContext
import rpi.util.Expressions._
import rpi.util.Infos.InstanceInfo
import rpi.util.Namespace
import rpi.util.Statements._
import viper.silver.ast

class QueryBuilder(protected val context: Context) extends CheckExtender with Folding {

  private var namespace: Namespace = _

  private var query: QueryContext = _

  private def configuration: Configuration =
    context.configuration

  def framingQuery(hypothesis: Hypothesis): (ast.Program, QueryContext) = {
    clear()
    ???
  }

  def basicQuery(checks: Seq[Check], hypothesis: Hypothesis): (ast.Program, QueryContext) = {
    clear()

    val methods = checks.map { check =>
      val body = process(check, hypothesis)
      buildMethod(check.name, body)
    }

    val program = buildProgram(methods, hypothesis)

    (program, query)
  }

  protected override def instrument(instrumented: ast.Stmt, hypothesis: Hypothesis): Unit =
    instrumented match {
      case ast.Seqn(statements, _) =>
        statements.foreach { statement => instrument(statement, hypothesis) }
      case ast.Inhale(expression) =>
        expression match {
          case placeholder: ast.PredicateAccessPredicate =>
            // get specification
            val instance = context.instance(placeholder.loc)
            val body = hypothesis.getPredicateBody(instance)
            // inhale placeholder predicate
            if (configuration.noInlining()) {
              // inhale and unfold predicate
              addInhale(placeholder)
              addUnfold(placeholder)
            } else {
              // inhale predicate body
              val info = InstanceInfo(instance)
              addInhale(body, info)
            }
            // unfold and save
            // TODO: depth
            unfold(body)(0, hypothesis)
            saveSnapshot(instance)
          case _ =>
            addInhale(expression)
        }
      case ast.Exhale(expression) =>
        expression match {
          case placeholder: ast.PredicateAccessPredicate =>
            // get specification
            val instance = context.instance(placeholder.loc)
            val body = hypothesis.getPredicateBody(instance)
            // save and fold
            // TODO: depth and annotations
            implicit val label: String = saveSnapshot(instance)
            if (configuration.useAnnotations()) {
              val annotations = Seq.empty
              foldWithAnnotations(body, annotations)(0, hypothesis, savePermission)
            } else fold(body)(0, hypothesis, savePermission)
            // exhale placeholder predicate
            if (configuration.noInlining()) {
              // fold and exhale predicate
              addFold(placeholder)
              addExhale(placeholder)
            } else {
              // exhale predicate body
              val info = InstanceInfo(instance)
              addExhale(body, info)
            }
          case _ =>
            addExhale(expression)
        }
      case _ => ???
    }

  private def saveSnapshot(instance: Instance): String = {
    // generate unique snapshot label
    val name = namespace.uniqueIdentifier(Names.snapshot, Some(0))
    query.addSnapshot(name, instance)
    // save values of variables
    instance
      .arguments
      .foreach {
        case variable: ast.LocalVar =>
          saveValue(s"${name}_${variable.name}", variable)
      }
    // save values of atoms
    instance
      .actualAtoms
      .zipWithIndex
      .foreach {
        case (atom, index) =>
          saveAtom(s"${name}_$index", atom)
      }
    // add label
    addLabel(name)
    // return snapshot label
    name
  }

  /**
    * Saves the permission value if the given expression is a field access or a predicate access.
    *
    * @param expression The expression.
    * @param guards     The collected guards.
    * @param label      The implicitly passed label for the current state snapshot
    */
  private def savePermission(expression: ast.Exp, guards: Seq[ast.Exp])(implicit label: String): Unit =
    expression match {
      case ast.FieldAccessPredicate(resource, _) =>
        savePermission(resource, guards)
      case ast.PredicateAccessPredicate(resource, _) =>
        savePermission(resource, guards)
      case _ => // do nothing
    }

  /**
    * Saves the permission value of the given location access.
    *
    * @param access The access.
    * @param guards The collected guards.
    * @param label  The implicitly passed label for the current state snapshot.
    */
  private def savePermission(access: ast.LocationAccess, guards: Seq[ast.Exp])(implicit label: String): Unit = {

    def extractConditions(expression: ast.Exp): Seq[ast.Exp] =
      expression match {
        case access: ast.FieldAccess =>
          val name = query.getName(label, access)
          val variable = ast.LocalVar(name, ast.Perm)()
          Seq(ast.PermGtCmp(variable, ast.NoPerm()())())
        case _ => Seq.empty
      }

    // generate unique name
    val name = namespace.uniqueIdentifier(Names.permission, Some(0))
    query.addName(label, access, name)

    //  conditions under which we have the permissions to talk about the given access.
    val conditions = access match {
      case ast.FieldAccess(receiver, _) =>
        extractConditions(receiver)
      case ast.PredicateAccess(arguments, _) =>
        arguments.flatMap { argument => extractConditions(argument) }
    }
    // conditionally save value
    val value = makeTernary(guards ++ conditions, makeCurrent(access), makeNone)
    saveValue(name, value)
  }

  /**
    * Saves the value of the given atom in a variable with the given name.
    *
    * @param name The name of the variable.
    * @param atom The atom to save.
    */
  private def saveAtom(name: String, atom: ast.Exp): Unit =
    if (configuration.noBranching()) saveValue(name, atom)
    else {
      // create conditional assignment
      val variable = makeBoolean(name)
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
    val variable = makeVariable(name, expression.typ)
    addAssign(variable, expression)
  }

  private def clear(): Unit = {
    namespace = context.namespace
    query = new QueryContext(configuration)
  }

  private def buildProgram(methods: Seq[ast.Method], hypothesis: Hypothesis): ast.Program = {
    val input = context.input
    val fields = {
      if (configuration.useAnnotations()) input.fields
      else magic +: input.fields
    }
    val predicates = {
      val existing = input.predicates
      val inferred = Seq.empty // TODO:
      existing ++ inferred
    }
    ast.Program(input.domains, fields, input.functions, predicates, methods, input.extensions)()
  }

  private def buildMethod(name: String, body: ast.Seqn): ast.Method = {
    val declarations = body
      .deepCollect { case variable: ast.LocalVar => variable }
      .distinct
      .map { variable => makeDeclaration(variable) }
    val scoped = makeSequence(body.ss, declarations)
    ast.Method(name, Seq.empty, Seq.empty, Seq.empty, Seq.empty, Some(scoped))()
  }

}