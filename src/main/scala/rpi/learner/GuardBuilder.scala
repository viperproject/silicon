package rpi.learner

import rpi.{Names, Settings}
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
    val body = buildExpression(template.body, atoms)
    // TODO: Incorporate truncation guard into template.
    if (template.name == Names.recursive && Settings.useSegments) {
      val Seq(first, second) = template.parameters.map { parameter => parameter.localVar }
      val truncationGuard = ast.NeCmp(first, second)()
      ast.Implies(truncationGuard, body)()
    } else body
  }

  /**
    * Builds the expression corresponding to the given template expression.
    *
    * @param expression The template expression to build.
    * @param atoms    The atoms used to build the guard.
    * @return The resource.
    */
  private def buildExpression(expression: TemplateExpression, atoms: Seq[ast.Exp]): ast.Exp =
    expression match {
      case Conjunction(conjuncts) =>
        val built = conjuncts.map { conjunct => buildExpression(conjunct, atoms) }
        bigAnd(built)
      case Resource(guardId, access) =>
        val guard = buildGuard(guardId, atoms)
        val accessPredicate = buildAccessPredicate(access)
        ast.Implies(guard, accessPredicate)()
      case choice@Choice(choiceId, options, body) =>
        val built = buildExpression(body, atoms)
        val name = s"t_$choiceId"
        val option = getOption(choice)
        val x = built.transform {
          case ast.LocalVar(`name`, _) => option
        }
        x
    }

  private def getOption(choice: Choice): ast.Exp =
    choice
      .options
      .zipWithIndex
      .find { case (_, index) =>
        model.getOrElse(s"c_${choice.choiceId}_$index", false)
      }
      .map { case (option, _) => option }
      .get

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
