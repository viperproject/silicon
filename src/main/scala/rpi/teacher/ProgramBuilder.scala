package rpi.teacher

import viper.silver.ast._

class ProgramBuilder(context: Context) {
  private var parameters: Seq[LocalVarDecl] = Seq.empty

  private var declarations: Seq[Declaration] = Seq.empty

  private var preconditions: Seq[Exp] = Seq.empty

  private var postconditions: Seq[Exp] = Seq.empty

  private var statements: Seq[Stmt] = Seq.empty

  def initialize(): Unit = {
    context.initials.foreach { case (initial, variable) =>
      addParameter(initial)
      addStatement(LocalVarAssign(variable, initial)())
    }
  }

  def addPrecondition(expression: Exp): Unit = preconditions :+= expression

  def addPostconditions(expression: Exp): Unit = postconditions :+= expression

  def addStatement(statement: Stmt): Unit = statement match {
    case Seqn(stmts, _) => stmts.foreach(addStatement)
    case _ => statements :+= statement
  }

  def buildMethod(): Method = {
    val formalArgs = context.method.formalArgs ++ parameters
    val exhales = postconditions.map(Exhale(_)())
    val body = Seqn(statements ++ exhales, context.declarations ++ declarations)()
    context.method.copy(
      formalArgs = formalArgs,
      pres = preconditions.map(rename),
      body = Some(body)
    )(NoPosition, NoInfo, NoTrafos)
  }

  def buildProgram(): Program = {
    val method = buildMethod()
    context.program.copy(methods = Seq(method))(NoPosition, NoInfo, NoTrafos)
  }

  private def addParameter(variable: LocalVar): Unit = {
    val declaration = LocalVarDecl(variable.name, variable.typ)()
    parameters :+= declaration
  }

  private def addDeclaration(declaration: Declaration): Unit = declarations :+= declaration

  private def rename(expression: Exp): Exp = expression.transform {
    case variable: LocalVar => context.reverse(variable)
  }
}
