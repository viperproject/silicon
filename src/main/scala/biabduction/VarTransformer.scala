package viper.silicon.biabduction

import viper.silicon.interfaces.{Failure, Success}
import viper.silicon.resources.{FieldID, PredicateID}
import viper.silicon.rules.{chunkSupporter, evaluator}
import viper.silicon.rules.chunkSupporter.findChunk
import viper.silicon.state.terms.{BuiltinEquals, Term, Var, sorts}
import viper.silicon.state.{BasicChunk, ChunkIdentifier, Heap, State, terms}
import viper.silicon.verifier.Verifier
import viper.silver.ast._
import viper.silver.verifier.PartialVerificationError
import viper.silver.verifier.errors.Internal

case class VarTransformer(s: State, v: Verifier, targetVars: Map[AbstractLocalVar, Term], targetHeap: Heap, strict: Boolean = true) {

  val pve: PartialVerificationError = Internal()

  // The symbolic values of the target vars in the store. Everything else is an attempt to match things to these terms
  //val targetMap: Map[Term, AbstractLocalVar] = targets.view.map(localVar => s.g.get(localVar).get -> localVar).toMap
  val directTargets = targetVars.map(_.swap)
  val pointsTargets = targetHeap.values.collect {
    case c: BasicChunk if c.resourceID == FieldID && directTargets.contains(c.args.head) =>
      c.snap -> FieldAccess(directTargets(c.args.head), abductionUtils.getField(c.id, s.program))()
  }.toMap
  val targets: Map[Term, Exp] = directTargets ++ pointsTargets

  // Current chunks as a map
  //val points: Map[Term, Term] = s.h.values.collect { case c: BasicChunk if c.resourceID == FieldID => c.args.head -> c.snap }.toMap

  // All other terms that might be interesting. Currently everything in the store and everything in field chunks
  val currentTerms: Seq[Term] = (s.g.values.values ++ s.h.values.collect { case c: BasicChunk if c.resourceID == FieldID => Seq(c.args.head, c.snap) }.flatten).toSeq //.collect { case t: Var => t }

  // Ask the decider whether any of the terms are equal to a target.
  val matches: Map[Term, Exp] = currentTerms.map { t =>
    t -> targets.collectFirst { case (t1, e) if t.sort == t1.sort && v.decider.check(BuiltinEquals(t, t1), Verifier.config.checkTimeout()) => e }
  }.collect { case (t2, Some(e)) => t2 -> e }.toMap

  // Field Chunks where the snap is equal to a known alias. This is only relevant for expression, not for chunks I think.
  //val snaps: Seq[BasicChunk] = s.h.values.collect { case c: BasicChunk if c.resourceID == FieldID && aliases.contains(c.snap) => c }.toSeq

  def transformTerm(t: Term): Option[Exp] = {

    t match {
      case terms.FullPerm => Some(FullPerm()())
      case _ => matches.get(t)
      /*/ Check for direct aliases
      val direct = matches.get(t)
      if (direct.isDefined) {
        direct
      } else {
        // Check for field accesses pointing to the term
        points.collectFirst { case (f, v) if v == t && matches.contains(f) => FieldAccess(matches(f), s.program.fields.head)() }
      }*/
    }
  }

  def onlyTargets(e: Exp): Boolean = {
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

    val transformed = e.transform {
      case fa: FieldAccess =>
        var t: Term = terms.Unit
        // TODO if we ever call this on state that has been abduced, we might need to access the "lost chunks" here
        val res = evaluator.eval(s, fa, pve, v)((_, t2, _) => {
          t = t2
          Success()
        })
        res match {
          case _: Success => transformTerm(t).getOrElse(fa)
          case _ => fa
        }
      case lv: LocalVar => transformTerm(s.g(lv)).getOrElse(lv)
    }

    //val varMap = e.collect { case lc: LocalVar => lc -> transformTerm(s.g(lc)) }.collect { case (k, Some(v)) => k -> v }.toMap

    //val onlyVars = e.transform {
    //  case lc: LocalVar if !targets.contains(lc) => varMap.getOrElse(lc, lc)
    //}

    //val accesses = onlyVars.transform {
    //  // TODO this will not catch z.next.next -> x
    //  case fa@FieldAccess(rcv: LocalVar, _) if !onlyTargets(fa) =>
    //    snaps.collectFirst { case c: BasicChunk if c.args.head == s.g(rcv) => matches(c.snap) }.getOrElse(fa)
    //}

    if (strict && !onlyTargets(transformed)) {
      None
    } else {
      Some(transformed)
    }
  }
}
