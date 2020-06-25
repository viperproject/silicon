package rpi.teacher

import viper.silver.ast._



class ProgramBuilder(context: Context) {
  private var declarations: Seq[Declaration] = Seq.empty

  private var statements: Seq[Stmt] = Seq.empty

  def initialize(): Unit = {
    context.initials.foreach { case (initial, variable) =>
      addDeclaration(LocalVarDecl(initial.name, initial.typ)())
      addStatement(LocalVarAssign(variable, initial)())
    }
  }

  def initialize(variable: LocalVar): LocalVar = {
    val initial = LocalVar(s"${variable.name}_init", variable.typ)()
    val assignment = LocalVarAssign(variable, initial)()
    addDeclaration(initial)
    addStatement(assignment)
    initial
  }

  def inhale(expression: Exp): Unit = addStatement(Inhale(expression)())

  def exhale(expression: Exp): Unit = addStatement(Exhale(expression)())

  def execute(statement: Stmt): Unit = statement match {
    case Seqn(stmts, _) => stmts.foreach(addStatement)
    case _ => addStatement(statement)
  }

  def buildMethod(): Method = {
    val body = Seqn(statements, context.declarations ++ declarations)()
    context.method.copy(body = Some(body))(NoPosition, NoInfo, NoTrafos)
  }

  def buildProgram(): Program = {
    val method = buildMethod()
    context.program.copy(methods = Seq(method))(NoPosition, NoInfo, NoTrafos)
  }

  private def addDeclaration(variable: LocalVar): Unit = {
    val declaration = LocalVarDecl(variable.name, variable.typ)()
    addDeclaration(declaration)
  }

  private def addDeclaration(declaration: Declaration): Unit = declarations :+= declaration

  private def addStatement(statement: Stmt): Unit = statements :+= statement
}
