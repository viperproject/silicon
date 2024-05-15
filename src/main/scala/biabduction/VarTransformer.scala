package viper.silicon.biabduction

import viper.silicon.interfaces.state.NonQuantifiedChunk
import viper.silicon.resources.{FieldID, PredicateID}
import viper.silicon.rules.chunkSupporter.findChunk
import viper.silicon.state.terms.{BuiltinEquals, Term}
import viper.silicon.state._
import viper.silicon.verifier.Verifier
import viper.silver.ast._
import viper.silver.verifier.PartialVerificationError
import viper.silver.verifier.errors.Internal

case class VarTransformer(s: State, v: Verifier, targetVars: Map[AbstractLocalVar, Term], targetHeap: Heap, strict: Boolean = true) {

  val pve: PartialVerificationError = Internal()

  // The symbolic values of the target vars in the store. Everything else is an attempt to match things to these terms
  //val targetMap: Map[Term, AbstractLocalVar] = targets.view.map(localVar => s.g.get(localVar).get -> localVar).toMap
  private val directTargets = targetVars.map(_.swap)
  private val pointsTargets = targetHeap.values.collect {
    case c: BasicChunk if c.resourceID == FieldID && directTargets.contains(c.args.head) =>
      c.snap -> FieldAccess(directTargets(c.args.head), abductionUtils.getField(c.id, s.program))()
  }.toMap
  val targets: Map[Term, Exp] = directTargets ++ pointsTargets

  // All other terms that might be interesting. Currently everything in the store and everything in field chunks
  private val currentTerms: Seq[Term] = (s.g.values.values ++ s.h.values.collect { case c: BasicChunk if c.resourceID == FieldID => Seq(c.args.head, c.snap) }.flatten).toSeq.distinct //.collect { case t: Var => t }

  // Ask the decider whether any of the terms are equal to a target.
  // TODO the decider is an object which changes. So the path conditions go away. We need to do this earlier
  val matches: Map[Term, Exp] = currentTerms.map { t =>
    t -> targets.collectFirst { case (t1, e) if t.sort == t1.sort && v.decider.check(BuiltinEquals(t, t1), Verifier.config.checkTimeout()) => e }
  }.collect { case (t2, Some(e)) => t2 -> e }.toMap

  def transformTerm(t: Term): Option[Exp] = {

    t match {
      case terms.FullPerm => Some(FullPerm()())
      case _ => matches.get(t)
    }
  }

  private def onlyTargets(e: Exp): Boolean = {
    val vars = e.collect { case lv: LocalVar => lv }.toSeq
    vars.forall(targetVars.contains(_))
  }

  def transformChunk(b: BasicChunk): Option[Exp] = {

    val rcv = transformTerm(b.args.head)
    (b, rcv) match {
      case (_, None) => None
      case (BasicChunk(FieldID, _, _, _, _), rcv) => Some(FieldAccessPredicate(FieldAccess(rcv.get, abductionUtils.getField(b.id, s.program))(), transformTerm(b.perm).get)())
      case (BasicChunk(PredicateID, _, _, _, _), rcv) => Some(abductionUtils.getPredicate(s.program, rcv.get, transformTerm(b.perm).get))
    }
  }

  def transformExp(e: Exp): Option[Exp] = {

    // TODO we need to be stricter here. If we can't find a match for a exp which uses
    // input vars, then we need to fail (see hidden.vpr)
    val transformed = e.transform {
      case fa@FieldAccess(lv: LocalVar, _) =>
        val args = List(s.g.get(lv).get)
        val resource = fa.res(s.program)
        val id = ChunkIdentifier(resource, s.program)
        findChunk[NonQuantifiedChunk](s.h.values, id, args, v) match {
          case Some(c) =>
            transformTerm(c.snap).getOrElse(fa)
          case None => fa
        }
      case fa@FieldAccess(rec, _) =>
        val rcv = transformExp(rec).getOrElse(rec)
        FieldAccess(rcv, fa.field)()
      case lv: LocalVar => transformTerm(s.g(lv)).getOrElse(lv)
    }
    if (strict && !onlyTargets(transformed)) {
      None
    } else {
      Some(transformed)
    }
  }
}
