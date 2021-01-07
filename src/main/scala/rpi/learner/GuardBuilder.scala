package rpi.learner

import rpi.Settings
import rpi.util.Expressions
import viper.silver.ast

class GuardBuilder(learner: Learner, constraints: Seq[ast.Exp]) {

  import Expressions._

  private val model: Map[String, Boolean] = {
    val solver = learner.solver
    solver.solve(constraints)
  }

  /**
    * Builds the body of the given template.
    *
    * @param template The template.
    * @return The body.
    */
  def buildBody(template: Template): ast.Exp = {
    val atoms = template.atoms
    val conjuncts = template.body.map { resource => buildResource(resource, atoms) }
    simplify(bigAnd(conjuncts))
  }

  /**
    * Builds the given resource including its guard.
    *
    * @param resource The resource to build.
    * @param atoms    The atoms used to build the guard.
    * @return The resource.
    */
  private def buildResource(resource: Resource, atoms: Seq[ast.Exp]): ast.Exp = {
    val guard = buildGuard(resource.guardId, atoms)
    val accessPredicate = buildAccessPredicate(resource.access)
    ast.Implies(guard, accessPredicate)()
  }

  /**
    * Builds the guard with the given id.
    *
    * @param guardId The id of the guard to build.
    * @param atoms   The atoms used to build the guard.
    * @return The guard.
    */
  private def buildGuard(guardId: Int, atoms: Seq[ast.Exp]): ast.Exp = {
    val clauses = for (j <- 0 until Settings.maxClauses) yield {
      val clauseActivation = model.getOrElse(s"x_${guardId}_$j", false)
      if (clauseActivation) {
        val literals = atoms.zipWithIndex.map {
          case (atom, i) => model
            .get(s"y_${guardId}_${i}_$j")
            .flatMap { literalActivation =>
              if (literalActivation) model
                .get(s"s_${guardId}_${i}_$j")
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

  /**
    * Builds an access predicate for the given access.
    *
    * @param access The access.
    * @return The predicate access.
    */
  private def buildAccessPredicate(access: ast.LocationAccess): ast.AccessPredicate =
    access match {
      case field: ast.FieldAccess => ast.FieldAccessPredicate(field, ast.FullPerm()())()
      case predicate: ast.PredicateAccess => ast.PredicateAccessPredicate(predicate, ast.FullPerm()())()
    }
}
