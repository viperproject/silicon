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

  // Ask the decider whether any of the terms are equal to a target.
  val matches: Map[Term, Exp] = resolveMatches()

  private def resolveMatches(): Map[Term, Exp] = {


    val allTerms: Seq[Term] = (s.g.values.values ++ s.h.values.collect { case c: BasicChunk if c.resourceID == FieldID => Seq(c.args.head, c.snap) }.flatten).toSeq.distinct //.collect { case t: Var => t }


    // The symbolic values of the target vars in the store. Everything else is an attempt to match things to these terms
    //val targetMap: Map[Term, AbstractLocalVar] = targets.view.map(localVar => s.g.get(localVar).get -> localVar).toMap
    val directTargets = targetVars.map(_.swap)

    val directAliases = allTerms.map { t =>
      t -> directTargets.collectFirst { case (t1, e) if t.sort == t1.sort && v.decider.check(BuiltinEquals(t, t1), Verifier.config.checkTimeout()) => e }
    }.collect { case (t2, Some(e)) => t2 -> e }.toMap

    resolveChunks(directAliases, targetHeap.values.collect { case c: BasicChunk
      if c.resourceID == FieldID && !(directAliases.contains(c.args.head) && directAliases.contains(c.snap)) => c }.toSeq, allTerms.filter(!directAliases.contains(_)))
  }

  private def resolveChunks(currentMatches: Map[Term, Exp], remainingChunks: Seq[BasicChunk], remainingTerms: Seq[Term]): Map[Term, Exp] = {
    remainingChunks.collectFirst { case c if currentMatches.contains(c.args.head) => c} match {
      case None => currentMatches
      case Some(c) =>
        val newExp = FieldAccess(currentMatches(c.args.head), abductionUtils.getField(c.id, s.program))()
        val newMatches = currentMatches ++ remainingTerms.collect{ case t if v.decider.check(BuiltinEquals(t, c.snap), Verifier.config.checkTimeout()) => t -> newExp }
        resolveChunks(newMatches, remainingChunks.filter(_ != c), remainingTerms.filter(!newMatches.contains(_)))
    }
  }

  def transformTerm(t: Term): Option[Exp] = {

    t match {
      case t if matches.contains(t) => matches.get(t)
      case terms.FullPerm => Some(FullPerm()())
      case terms.Null => Some(NullLit()())
      case _ => None
    }
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
              val existingChunkTerm = transformTerm(term)
              existingChunkTerm.get match {
                case nfa: FieldAccess => nfa

                // Due to heap representation this can sometimes happen
                case NullLit() =>
                  val rvcExp = transformExp(target)
                  FieldAccess(rvcExp.get, field)()
              }
            // Else we want to recurse and try to match the target
            case None =>
              val rvcExp = transformExp(target)
              FieldAccess(rvcExp.get, field)()
          }
        case lv: LocalVar => transformTerm(s.g(lv)).get
      }
      Some(res)
    } catch {
      case _: NoSuchElementException => None
    }
  }
}
