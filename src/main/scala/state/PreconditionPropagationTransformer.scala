package viper.silicon.state

import viper.silicon.rules.functionSupporter
import viper.silicon.state.terms.{And, App, HeapDepFun, Implies, Ite, Let, Literal, Not, Or, Quantification, Term, True}
import viper.silver.ast

object PreconditionPropagationTransformer {
  def transform(t: Term, p: ast.Program): Term = {
    val res = t match {
      case _:Literal => True()
      case And(ts) => And(transform(ts.head, p), Implies(ts.head, transform(And(ts.tail), p)))
      case Or(ts) => And(transform(ts.head, p), Implies(Not(ts.head), transform(Or(ts.tail), p)))
      case Implies(t0, t1) => And(transform(t0, p), Implies(t0, transform(t1, p)))
      case Ite(t, t1, t2) => And(transform(t, p), Ite(t, transform(t1, p), transform(t2, p)))
      case Let(bindings, body) => Let(bindings, transform(body, p))
      case Quantification(q, vars, body, triggers, name, isGlobal) =>
        val tBody = transform(body, p)
        if (tBody == True())
          True()
        else
          Quantification(q, vars, tBody, triggers, name, isGlobal)
      case App(hdf@HeapDepFun(id, _, _), args)  =>
        val funcName = id match {
          case SuffixedIdentifier(prefix, _, _) => prefix.name
          case _ => id.name
        }
        if (p.findFunction(funcName).pres.nonEmpty)
          And(args.map(transform(_, p)) :+ App(functionSupporter.preconditionVersion(hdf), args))
        else
          And(args.map(transform(_, p)))
      case other => And(other.subterms.map(transform(_, p)))
    }
    res
  }

}
