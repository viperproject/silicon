package viper.silicon.state

import viper.silicon.rules.functionSupporter
import viper.silicon.state.terms.{And, App, Forall, HeapDepFun, Implies, Ite, Let, Literal, Not, Or, Quantification, Term, True}
import viper.silver.ast


/**
  * Given a term t, returns a new term tr(t) that expresses that all applications of heap-dependent functions are
  * well-defined (in particular, that the abstract functions that represent their preconditions hold).
  * In general, after checking that t is well-defined, it is sound to assume tr(t).
  *
  * I.e., given
  *   fun(e1, ..., en)
  * where fun is a heap-dependent function with a precondition, it returns
  *   tr(e1) && ... && tr(en) && fun%precondition(e1, ..., en)
  * where the tr(ei) terms express that all function applications in the argument terms are well-defined.
  *
  * For &&, ||, and ==>, the transformation takes into account short-circuit semantics:
  * If A && B is well-defined, that means that A is well-defined, and if A is true, then B is well-defined as well.
  * Thus, the transformation of A && B is tr(A) && (A ==> tr(B)).
  */
object FunctionPreconditionTransformer {
  def transform(t: Term, p: ast.Program): Term = {
    val res = t match {
      case _:Literal => True()
      case And(ts) => And(transform(ts.head, p), Implies(ts.head, transform(And(ts.tail), p)))
      case Or(ts) => And(transform(ts.head, p), Implies(Not(ts.head), transform(Or(ts.tail), p)))
      case Implies(t0, t1) => And(transform(t0, p), Implies(t0, transform(t1, p)))
      case Ite(t, t1, t2) => And(transform(t, p), Ite(t, transform(t1, p), transform(t2, p)))
      case Let(bindings, body) =>
        And(And(bindings.map(b => transform(b._2, p))), Let(bindings, transform(body, p)))
      case Quantification(_, vars, body, triggers, name, isGlobal, weight) =>
        val tBody = transform(body, p)
        if (tBody == True()) {
          tBody
        } else {
          // We assume well-definedness for *all* possible values even for existential quantifiers
          // (since that is also what we check).
          Quantification(Forall, vars, tBody, triggers, name, isGlobal, weight)
        }
      case App(hdf@HeapDepFun(_, _, _), args)  =>
          And(args.map(transform(_, p)) :+ App(functionSupporter.preconditionVersion(hdf), args))
      case other => And(other.subterms.map(transform(_, p)))
    }
    res
  }

}
