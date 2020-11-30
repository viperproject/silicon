package rpi.learner

import rpi.Config
import rpi.util.Expressions
import viper.silver.{ast => sil}

class GuardBuilder(learner: Learner, constraints: Seq[sil.Exp]) {

  private val model: Map[String, Boolean] = {
    val solver = learner.solver
    solver.solve(constraints)
  }

  def buildBody(template: Template): sil.Exp = {
    val atoms = template.atoms
    val conjuncts = template
      .accesses
      .map { guarded => buildGuarded(guarded, atoms) }
    Expressions.simplify(Expressions.bigAnd(conjuncts))
  }

  def buildGuarded(guarded: Guarded, atoms: Seq[sil.Exp]): sil.Exp = {
    // extract guard from model
    val guard = {
      val id = guarded.id
      val clauses = for (j <- 0 until Config.maxClauses) yield {
        val clauseActivation = model.getOrElse(s"x_${id}_$j", false)
        if (clauseActivation) {
          val literals = atoms.zipWithIndex.map {
            case (atom, i) => model
              .get(s"y_${id}_${i}_$j")
              .flatMap { literalActivation =>
                if (literalActivation) model
                  .get(s"s_${id}_${i}_$j")
                  .map { sign => if (sign) atom else sil.Not(atom)() }
                else None
              }
              .getOrElse(sil.TrueLit()())
          }
          Expressions.bigAnd(literals)
        } else sil.FalseLit()()
      }
      Expressions.bigOr(clauses)
    }

    // build resource access
    val resource = guarded.access match {
      case access: sil.FieldAccess =>
        sil.FieldAccessPredicate(access, sil.FullPerm()())()
      case access: sil.PredicateAccess =>
        sil.PredicateAccessPredicate(access, sil.FullPerm()())()
    }

    // return guarded resource
    sil.Implies(guard, resource)()
  }
}
