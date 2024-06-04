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

case class VarTransformer(s: State, v: Verifier, targetVars: Map[AbstractLocalVar, Term], targetHeap: Heap) {

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

  private def safeEval(e: Exp): Option[Term] = {
    e match {
      case lv: LocalVar => Some(s.g(lv))
      case fa@FieldAccess(target, _) =>
        safeEval(target) match {
          case None => None
          case Some(arg) =>
            val args = List(arg)
            val resource = fa.res(s.program)
            val id = ChunkIdentifier(resource, s.program)
            findChunk[NonQuantifiedChunk](s.h.values, id, args, v) match {
              case Some(c) => Some(c.snap)
              case None => None
            }
        }
    }
  }

  // This is kinda tricky if the expression contains field accesses.
  // We do not get the guarantee that the chunks exist in the current state, so we can not evaluate them
  // directly
  def transformExp(e: Exp): Option[Exp] = {
    try {
      val res = e.transform {
        case fa@FieldAccess(target, field) =>
          safeEval(fa) match {
            // If the chunk exists in the current state, then we want to match the snap term
            case Some(term) =>
              transformTerm(term).get
            // Else we want to recurse and try to match the target
            case None => FieldAccess(transformExp(target).get, field)()
          }
        case lv: LocalVar => transformTerm(s.g(lv)).get
      }
      Some(res)
    } catch {
      case _: NoSuchElementException => None
    }
  }
}


//transformExp(target) match {
//case Some(res) => FieldAccess(res, field)()
//case None => safeEval(target) match {
//  case Some(res) => transformTerm(res).getOrElse(DummyNode)
//  case None => DummyNode
//}
//}

//case fa@FieldAccess(lv: LocalVar, _) =>
// Try to resolve the target
//  val args = List(s.g.get(lv).get)
//  val resource = fa.res(s.program)
//  val id = ChunkIdentifier(resource, s.program)
//  findChunk[NonQuantifiedChunk](s.h.values, id, args, v) match {
//    case Some(c) =>
//      transformTerm(c.snap).getOrElse(fa)
//    case None => fa
//  }
//case fa@FieldAccess(rec, _) =>
//  val rcv = transformExp(rec).getOrElse(rec)
//  FieldAccess(rcv, fa.field)()
