package rpi.teacher

import rpi._
import rpi.util.Expressions
import viper.silver.{ast => sil}

/**
  * Builds programs used to check hypotheses.
  *
  * @param teacher The pointer to the teacher.
  */
class ProgramBuilder(teacher: Teacher) {
  /**
    * Returns the pointer to the inference.
    *
    * @return The inference.
    */
  def inference: Inference = teacher.inference

  /**
    * Returns the pointer to the original program.
    *
    * @return The original program.
    */
  def original: sil.Program = inference.program

  private var inits: Seq[sil.LocalVarDecl] = Seq.empty

  private var stmts: Seq[sil.Stmt] = Seq.empty

  def buildCheck(triple: Triple, hypothesis: Seq[sil.Predicate]): sil.Program = {
    val specifications = inference.specifications
    val prePred = triple.pres.collectFirst { case pred: sil.PredicateAccessPredicate => pred }.get
    val postPred = triple.posts.collectFirst { case pred: sil.PredicateAccessPredicate => pred }.get
    val preSpec = specifications(prePred.loc.predicateName)
    val postSpec = specifications(postPred.loc.predicateName)

    // clear
    clear()

    // save variables
    saveVars(triple)
    // assume pre-condition and loop condition
    triple.pres.foreach(addInhale)
    triple.pres.collect { case p: sil.PredicateAccessPredicate => p }.foreach(addUnfold)
    // pre-state
    val preAtoms = preSpec.adaptedAtoms(prePred.loc.args)
    preAtoms.zipWithIndex.foreach { case (atom, i) => saveExp(s"${Labels.PRE_STATE}_p_$i", atom) }
    addLabel(Labels.PRE_STATE)

    // execute loop body
    addStmt(triple.body)

    // reflect on permission amounts
    val subs = {
      val name = postSpec.variables.map { variable => variable.name }
      val arguments = postPred.loc.args
      name.zip(arguments).toMap
    }

    hypothesis
      .find(_.name == postPred.loc.predicateName).get.body.get
      .collect { case pred: sil.FieldAccessPredicate => pred.loc }
      .foreach {
        access: sil.FieldAccess =>
          // formal to actual transformation (maybe we can reuse code for access paths?)
          val location = access.transform { case sil.LocalVar(name, _) => subs(name) }
          // assign current perm to variable
          val lhs = sil.LocalVar(s"perm_${Expressions.toSeq(location).mkString("_")}", sil.Perm)()
          val rhs = sil.CurrentPerm(location)()
          addStmt(sil.LocalVarAssign(lhs, rhs)())
      }
    // post-state
    val postAtoms = postSpec.adaptedAtoms(postPred.loc.args)
    postAtoms.zipWithIndex.foreach { case (atom, i) => saveExp(s"${Labels.POST_STATE}_p_$i", atom) }
    addLabel(Labels.POST_STATE)
    // assume post-condition
    triple.posts.collect { case p: sil.PredicateAccessPredicate => p }.foreach(addFold)
    triple.posts.foreach(addExhale)
    // return program
    buildProgram(hypothesis)
  }

  private def clear(): Unit = {
    inits = Seq.empty
    stmts = Seq.empty
  }

  private def addStmt(stmt: sil.Stmt): Unit = stmts :+= stmt

  private def saveVars(triple: Triple): Unit = {
    val elems = triple.pres ++ triple.body.ss ++ triple.posts
    elems.flatMap(_.deepCollect { case variable: sil.LocalVar => variable })
      .distinct
      .foreach { variable =>
        val init = sil.LocalVar(s"${variable.name}_init", variable.typ)()
        addStmt(sil.LocalVarAssign(variable, init)())
      }
  }

  private def addLabel(name: String): Unit = addStmt(sil.Label(name, Seq.empty)())

  private def addInhale(exp: sil.Exp): Unit = addStmt(sil.Inhale(exp)())

  private def addExhale(exp: sil.Exp): Unit = addStmt(sil.Exhale(exp)())

  private def addUnfold(pred: sil.PredicateAccessPredicate): Unit = addStmt(sil.Unfold(pred)())

  private def addFold(pred: sil.PredicateAccessPredicate): Unit = addStmt(sil.Fold(pred)())

  private def saveExp(name: String, exp: sil.Exp): Unit = {
    val variable = sil.LocalVar(name, sil.Bool)()
    val thn = sil.Seqn(Seq(sil.LocalVarAssign(variable, sil.BoolLit(b = true)())()), Seq.empty)()
    val els = sil.Seqn(Seq(sil.LocalVarAssign(variable, sil.BoolLit(b = false)())()), Seq.empty)()
    addStmt(sil.If(exp, thn, els)())
  }

  private def buildBody(): sil.Seqn = {
    val vars = stmts.flatMap(_.deepCollect { case v: sil.LocalVar => v }).distinct
    val decls = vars.map(v => sil.LocalVarDecl(v.name, v.typ)())
    sil.Seqn(stmts, decls)()
  }

  private def buildMethod(): sil.Method = {
    val name = "check"
    val args = Seq.empty
    val returns = Seq.empty
    val pres = Seq.empty
    val posts = Seq.empty
    val body = Some(buildBody())
    sil.Method(name, args, returns, pres, posts, body)()
  }

  private def buildProgram(hypothesis: Seq[sil.Predicate]): sil.Program = {
    val domains = Seq.empty
    val fields = original.fields
    val functions = Seq.empty
    val predicates = hypothesis
    val methods = Seq(buildMethod())
    val extensions = Seq.empty
    sil.Program(domains, fields, functions, predicates, methods, extensions)()
  }
}
