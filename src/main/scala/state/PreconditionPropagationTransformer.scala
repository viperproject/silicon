package viper.silicon.state

import viper.silicon.rules.functionSupporter
import viper.silicon.state.terms.{And, App, HeapDepFun, Implies, Ite, Let, Literal, Not, Or, Quantification, Term, True}

object PreconditionPropagationTransformer {
  def transform(t: Term): Term = t match {
    case _:Literal => True()
    case And(ts) => And(transform(ts.head), Implies(ts.head, transform(And(ts.tail))))
    case Or(ts) => And(transform(ts.head), Implies(Not(ts.head), transform(Or(ts.tail))))
    case Implies(t0, t1) => And(transform(t0), Implies(t0, transform(t1)))
    case Ite(t, t1, t2) => And(transform(t), Ite(t, transform(t1), transform(t2)))
    case Let(bindings, body) => Let(bindings, transform(body))
    case Quantification(q, vars, body, triggers, name, isGlobal) => Quantification(q, vars, transform(body), triggers, name, isGlobal)
    case App(hdf@HeapDepFun(_, _, _), args) => And(args.map(transform(_)) :+ App(functionSupporter.preconditionVersion(hdf), args))
    case other => And(other.subterms.map(transform(_)))
  }

}
