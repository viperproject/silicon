package rpi.learner

import rpi._
import rpi.util.Expressions
import viper.silver.{ast => sil}

class GuardSolver(learner: Learner, constraints: sil.Exp) {
  private lazy val model = {
    val solver = learner.solver
    solver.solve(constraints)
  }

  private lazy val fields = {
    val program = learner.inference.program
    program.fields.map { field => field.name -> field }.toMap
  }

  def solveTemplate(template: Template): sil.Exp = {
    val atoms = template.specification.atoms
    val conjuncts = template.resources.map { resource => createGuarded(resource, atoms) }
    Expressions.bigAnd(conjuncts)
  }

  private def createGuarded(guarded: Guarded, atoms: Seq[sil.Exp]): sil.Exp = {
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
      Expressions.simplify(Expressions.bigOr(clauses))
    }

    val resource = guarded.resource match {
      case Permission(path) =>
        val location = createField(path)
        sil.FieldAccessPredicate(location, sil.FullPerm()())()
      case Predicate(name, arguments) =>
        val location = sil.PredicateAccess(arguments.map(createPath), name)()
        sil.PredicateAccessPredicate(location, sil.FullPerm()())()
    }

    sil.Implies(guard, resource)()
  }

  private def createPath(path: AccessPath): sil.Exp = path match {
    case VariablePath(name) => sil.LocalVar(name, sil.Ref)()
    case _ => createField(path)
  }

  private def createField(path: AccessPath): sil.FieldAccess = path match {
    case FieldPath(receiver, field) =>
      sil.FieldAccess(createPath(receiver), fields(path.last))()
  }
}
