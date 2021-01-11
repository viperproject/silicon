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
    buildExpression(template.body, atoms)
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
        val builtConjuncts = conjuncts.map { conjunct => buildExpression(conjunct, atoms) }
        bigAnd(builtConjuncts)
      case Resource(guardId, access) =>
        val builtGuard = buildGuard(guardId, atoms)
        val builtResource = buildResource(access)
        ast.Implies(builtGuard, builtResource)()
      case Choice(choiceId, options, body) =>
        // build body
        val builtBody = buildExpression(body, atoms)
        // get option
        val name = s"t_$choiceId"
        val option = getOption(choiceId, options)
        // adapt body according to picked option
        builtBody.transform {
          case ast.LocalVar(`name`, _) => option
        }
      case Truncation(condition, body) =>
        val builtBody = buildExpression(body, atoms)
        ast.Implies(condition, builtBody)()
    }

  private def getOption(choiceId: Int, options: Seq[ast.Exp]): ast.Exp =
    options
      .zipWithIndex
      .find { case (_, index) =>
        model.getOrElse(s"c_${choiceId}_$index", false)
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
  private def buildResource(access: ast.LocationAccess): ast.AccessPredicate =
    access match {
      case field: ast.FieldAccess => ast.FieldAccessPredicate(field, ast.FullPerm()())()
      case predicate: ast.PredicateAccess => ast.PredicateAccessPredicate(predicate, ast.FullPerm()())()
    }
}
