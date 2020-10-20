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
    val specs = learner.inference.specs
    val atoms = specs(template.name).atoms

    val x = template.resources.map { resource => createGuarded(resource, atoms) }
    Expressions.bigAnd(x)
  }

  private def createGuarded(guarded: Guarded, atoms: Seq[sil.Exp]): sil.Exp = {
    // complexity parameter
    // TODO: Make config.
    val k = 1

    val guard = {
      val id = guarded.id
      val clauses = for (j <- 0 until k) yield {
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
        val location = createPath(path)
        sil.FieldAccessPredicate(location, sil.FullPerm()())()
      case _ => ???
    }

    sil.Implies(guard, resource)()
  }

  private def createPath(path: AccessPath): sil.FieldAccess = {
    val receiver = path.dropLast match {
      case VariablePath(name) => sil.LocalVar(name, sil.Ref)()
      case other => createPath(other)
    }
    sil.FieldAccess(receiver, fields(path.last))()
  }


}
