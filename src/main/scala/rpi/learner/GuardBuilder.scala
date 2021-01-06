package rpi.learner

import rpi.Settings
import rpi.util.Expressions
import viper.silver.ast

class GuardBuilder(learner: Learner, constraints: Seq[ast.Exp]) {

  private val model: Map[String, Boolean] = {
    val solver = learner.solver
    solver.solve(constraints)
  }

  def buildBody(template: Template): ast.Exp = {
    val atoms = template.atoms
    val conjuncts = template
      .accesses
      .map { guarded => buildGuarded(guarded, atoms) }
    Expressions.simplify(Expressions.bigAnd(conjuncts))
  }

  def buildGuarded(guarded: Guarded, atoms: Seq[ast.Exp]): ast.Exp = {
    // extract guard from model
    val guard = {
      val id = guarded.id
      val clauses = for (j <- 0 until Settings.maxClauses) yield {
        val clauseActivation = model.getOrElse(s"x_${id}_$j", false)
        if (clauseActivation) {
          val literals = atoms.zipWithIndex.map {
            case (atom, i) => model
              .get(s"y_${id}_${i}_$j")
              .flatMap { literalActivation =>
                if (literalActivation) model
                  .get(s"s_${id}_${i}_$j")
                  .map { sign => if (sign) atom else ast.Not(atom)() }
                else None
              }
              .getOrElse(ast.TrueLit()())
          }
          Expressions.bigAnd(literals)
        } else ast.FalseLit()()
      }
      Expressions.bigOr(clauses)
    }

    // build resource access
    val resource = guarded.access match {
      case access: ast.FieldAccess =>
        ast.FieldAccessPredicate(access, ast.FullPerm()())()
      case access: ast.PredicateAccess =>
        ast.PredicateAccessPredicate(access, ast.FullPerm()())()
    }

    // return guarded resource
    ast.Implies(guard, resource)()
  }
}
