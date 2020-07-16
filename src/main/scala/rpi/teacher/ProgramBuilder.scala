package rpi.teacher

import viper.silver.ast._

class ProgramBuilder(context: Context) {

  private var decls: Seq[Declaration] = Seq.empty

  private var stmts: Seq[Stmt] = Seq.empty

  def addInhale(exp: Exp): Unit = addStmt(Inhale(exp)())

  def addExhale(exp: Exp): Unit = addStmt(Exhale(exp)())

  def addLabel(name: String): Unit = addStmt(Label(name, Seq.empty)())

  def addStmt(stmt: Stmt): Unit = stmts :+= stmt

  def addDecl(decl: Declaration): Unit = decls :+= decl

  def saveValue(exp: Exp, name: String): Unit = {
    val variable = LocalVar(name, Bool)()
    val declaration = LocalVarDecl(name, Bool)()

    addDecl(declaration)

    val thn = Seqn(LocalVarAssign(variable, BoolLit(true)())() :: Nil, Seq.empty)()
    val els = Seqn(LocalVarAssign(variable, BoolLit(false)())() :: Nil, Seq.empty)()
    addStmt(If(exp, thn, els)())
  }

  def buildMethod(): Method = {
    val name = "foo"
    val args = context.args()
    val returns = Seq.empty
    val pres = Seq.empty
    val posts = Seq.empty
    val body = Some(Seqn(stmts, context.vars())())
    Method(name, args, returns, pres, posts, body)()
  }

  def buildProgram(): Program = {
    val domains = Seq.empty
    val fields = context.fields()
    val functions = Seq.empty
    val predicates = Seq.empty
    val methods = Seq(buildMethod())
    val extensions = Seq.empty
    Program(domains, fields, functions, predicates, methods, extensions)()
  }
}
