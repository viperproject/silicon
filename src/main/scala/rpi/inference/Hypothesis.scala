package rpi.inference

import rpi.{Names, Settings}
import rpi.util.Expressions._
import viper.silver.ast

/**
  * A hypothesis.
  */
case class Hypothesis(predicates: Map[String, ast.Predicate]) {

  lazy val lemmaMethods: Seq[ast.Method] =
    if (Settings.useSegments)
      predicates
        .get(Names.recursive)
        .flatMap { predicate => Lemmas.appendLemma(predicate) }
        .toSeq
    else Seq.empty

  def get(name: String): ast.Exp =
    predicates
      .get(name)
      .flatMap { predicate => predicate.body }
      .getOrElse(top)

  def get(instance: Instance): ast.Exp = {
    val body = get(instance.name)
    instance.toActual(body)
  }
}

object Lemmas {
  def appendLemma(predicate: ast.Predicate): Option[ast.Method] = {
    // get recursions
    val body = predicate.body.get
    val recursions = getRecursions(body)
    // only generate lemme if there is a recursion
    if (recursions.isEmpty) None
    else {
      assert(recursions.size == 1)
      // parameters and fields
      val parameters = ast.LocalVarDecl("z", ast.Ref)() +: predicate.formalArgs
      val Seq(first, previous, last) = parameters.map { parameter => parameter.localVar }
      val fields = getFields(body)
      // precondition and postcondition
      val precondition = Seq(instance(first, previous)) ++ fields ++ recursions
      val postcondition = Seq(instance(first, last))
      // create lemma method
      val method = ast.Method(Names.appendLemma, parameters, Seq.empty, precondition, postcondition, None)()
      Some(method)
    }
  }

  private def instance(from: ast.Exp, to: ast.Exp): ast.PredicateAccessPredicate = {
    val arguments = Seq(from, to)
    val access = ast.PredicateAccess(arguments, Names.recursive)()
    val permission = ast.FullPerm()()
    ast.PredicateAccessPredicate(access, permission)()
  }

  private def getRecursions(expression: ast.Exp, guards: Seq[ast.Exp] = Seq.empty): Seq[ast.Exp] =
    expression match {
      case ast.And(left, right) =>
        getRecursions(left, guards) ++ getRecursions(right, guards)
      case ast.Implies(guard, guarded) =>
        getRecursions(guarded, guards :+ guard)
      case ast.PredicateAccessPredicate(ast.PredicateAccess(Seq(next, last), _), _) =>
        val condition = ast.EqCmp(next, last)()
        val guarded = if (guards.isEmpty) condition else implies(bigAnd(guards), condition)
        Seq(guarded)
      case _ => Seq.empty
    }

  private def getFields(expression: ast.Exp, guards: Seq[ast.Exp] = Seq.empty): Seq[ast.Exp] =
    expression match {
      case ast.And(left, right) =>
        getFields(left, guards) ++ getFields(right, guards)
      case ast.Implies(guard, guarded) =>
        getFields(guarded, guards :+ guard)
      case field: ast.FieldAccessPredicate =>
        val guarded = if (guards.isEmpty) field else implies(bigAnd(guards), field)
        Seq(guarded)
      case _ =>
        Seq.empty
    }
}