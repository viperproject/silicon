package viper.silicon.biabduction

import viper.silicon.resources.{FieldID, PredicateID}
import viper.silicon.state.terms.{BuiltinEquals, Term, Var}
import viper.silicon.state.{BasicChunk, State, terms}
import viper.silicon.verifier.Verifier
import viper.silver.ast._

case class VarTransformer(s: State, v: Verifier, targets: Seq[LocalVar], strict: Boolean = true) {

  // The symbolic values of the target vars in the store. Everything else is an attempt to match things to these terms
  val targetMap: Map[Term, LocalVar] = targets.view.map(localVar => s.g.get(localVar).get -> localVar).toMap

  // Fields chunks as a map
  val points: Map[Term, Term] = s.h.values.collect { case c: BasicChunk if c.resourceID == FieldID => c.args.head -> c.snap }.toMap

  // All other terms that might be interesting. Currently everything in the store and everything in field chunks
  val allTerms: Seq[Term] = (s.g.values.values ++ s.h.values.collect { case c: BasicChunk if c.resourceID == FieldID => Seq(c.args.head, c.snap) }.flatten).collect {case t: Var => t}.toSeq

  // Ask the decider whether any of the terms are equal to a target.
  val aliases: Map[Term, LocalVar] = allTerms.map { t =>
    t -> targetMap.collectFirst { case (t1, e) if v.decider.check(BuiltinEquals(t, t1), Verifier.config.checkTimeout()) => e }
  }.collect { case (t2, Some(e)) => t2 -> e }.toMap

  // Field Chunks where the snap is equal to a known alias. This is only relevant for expression, not for chunks I think.
  val snaps: Seq[BasicChunk] = s.h.values.collect { case c: BasicChunk if c.resourceID == FieldID && aliases.contains(c.snap) => c }.toSeq

  def transformTerm(t: Term): Option[Exp] = {

    t match {
      case terms.FullPerm => Some(FullPerm()())
      case _ =>
        // Check for direct aliases
        val direct = aliases.get(t)
        if (direct.isDefined) {
          direct
        } else {
          // Check for field accesses pointing to the term
          points.collectFirst { case (f, v) if v == t && aliases.contains(f) => FieldAccess(aliases(f), s.program.fields.head)() }
        }
    }
  }

  def onlyTargets(e: Exp): Boolean = {
    val vars = e.collect { case lv: LocalVar => lv }.toSeq
    vars.forall(targets.contains(_))
  }

  def transformChunk(b: BasicChunk): Option[Exp] = {

    val rcv = transformTerm(b.args.head)
    (b, rcv) match {
      case (_, None) => None
      case (BasicChunk(FieldID, _, _, _, _), rcv) => Some(FieldAccessPredicate(FieldAccess(rcv.get, abductionUtils.getField(b.id, s.program))(), transformTerm(b.perm).get)())
      case (BasicChunk(PredicateID, _, _, _, _), rcv) => Some(abductionUtils.getPredicate(s.program, rcv.get, transformTerm(b.perm).get))
    }
  }

  // TODO the original work introduces logical vars representing the original input values. They attempt (I think) to transform
  // to these vars. See the "Rename" algorithm in the original paper.
  // At the end, they can be re-replaced by the input parameters. Do we have to do this?
  def transformExp(e: Exp): Option[Exp] = {

    val varMap = e.collect { case lc: LocalVar => lc -> transformTerm(s.g(lc)) }.collect { case (k, Some(v)) => k -> v }.toMap

    val onlyVars = e.transform {
      case lc: LocalVar if !targets.contains(lc) => varMap.getOrElse(lc, lc)
    }

    val accesses = onlyVars.transform {
      // TODO this will not catch z.next.next -> x
      case fa@FieldAccess(rcv: LocalVar, _) if !onlyTargets(fa) =>
        snaps.collectFirst { case c: BasicChunk if c.args.head == s.g(rcv) => aliases(c.snap) }.getOrElse(fa)
    }

    if (strict && !onlyTargets(accesses)) {
      None
    } else {
      Some(accesses)
    }
  }
}
