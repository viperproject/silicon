package viper.silicon.biabduction

import viper.silicon.interfaces.state.NonQuantifiedChunk
import viper.silicon.resources.{FieldID, PredicateID}
import viper.silicon.rules.chunkSupporter.findChunk
import viper.silicon.state.terms.{BuiltinEquals, Term, Var}
import viper.silicon.state._
import viper.silicon.verifier.Verifier
import viper.silver.ast
import viper.silver.ast._

import scala.annotation.tailrec

case class VarTransformer(s: State, v: Verifier, targetVars: Map[AbstractLocalVar, (Term, Option[ast.Exp])], targetHeap: Heap, newFieldChunks: Map[BasicChunk, LocationAccess] = Map()) {

  //val pve: PartialVerificationError = Internal()

  // Ask the decider whether any of the terms are equal to a target.
  val matches: Map[Term, Exp] = resolveMatches()

  val newChunkBySnap = newFieldChunks.map { case (c, fa: FieldAccess) => c.snap -> (c, fa) }

  private def resolveMatches(): Map[Term, Exp] = {

    val allTerms: Seq[Term] = (s.g.values.values.map { case (t1, _) => t1 }
      ++ s.h.values.collect { case c: BasicChunk if c.resourceID == FieldID => Seq(c.args.head, c.snap) }.flatten
      ++ targetVars.values.map(_._1)
      ++ v.decider.pcs.branchConditions.collect { case t => t.subterms.collect { case tVar: Var => tVar } }.flatten).toSeq.distinct

    // The symbolic values of the target vars in the store. Everything else is an attempt to match things to these terms
    //val targetMap: Map[Term, AbstractLocalVar] = targets.view.map(localVar => s.g.get(localVar).get -> localVar).toMap
    val directTargets = targetVars.map(_.swap)

    val directAliases = allTerms.map { t =>
      t -> directTargets.collectFirst { case ((t1, _), e) if t.sort == t1.sort && v.decider.check(BuiltinEquals(t, t1), Verifier.config.checkTimeout()) => e }
    }.collect { case (t2, Some(e)) => t2 -> e }.toMap

    val chunksToResolve = targetHeap.values.collect { case c: BasicChunk
      if c.resourceID == FieldID && !(directAliases.contains(c.args.head) && directAliases.contains(c.snap)) => c
    }.toSeq

    resolveChunks(directAliases, chunksToResolve, allTerms.filter(!directAliases.contains(_)))
  }

  @tailrec
  private def resolveChunks(currentMatches: Map[Term, Exp], remainingChunks: Seq[BasicChunk], remainingTerms: Seq[Term]): Map[Term, Exp] = {
    remainingChunks.collectFirst { case c if currentMatches.contains(c.args.head) => c } match {
      case None => currentMatches
      case Some(c) =>
        val newExp = FieldAccess(currentMatches(c.args.head), abductionUtils.getField(c.id, s.program))()
        val newMatches = currentMatches ++ remainingTerms.collect { case t if t.sort == c.snap.sort && v.decider.check(BuiltinEquals(t, c.snap), Verifier.config.checkTimeout()) => t -> newExp }
        resolveChunks(newMatches, remainingChunks.filter(_ != c), remainingTerms.filter(!newMatches.contains(_)))
    }
  }

  def transformTerm(t: Term): Option[Exp] = {

    t match {
      case t if matches.contains(t) => matches.get(t)
      case BuiltinEquals(t1, t2) => (transformTerm(t1), transformTerm(t2)) match {
        case (Some(e1), Some(e2)) =>
          Some(EqCmp(e1, e2)())
        case _ => None
      }
      case terms.FractionPermLiteral(r) => Some(FractionalPerm(IntLit(r.numerator)(), IntLit(r.denominator)())())
      case terms.FullPerm => Some(FullPerm()())
      case terms.Null => Some(NullLit()())
      case terms.Not(BuiltinEquals(t1, t2)) => (transformTerm(t1), transformTerm(t2)) match {
        case (Some(e1), Some(e2)) =>
          Some(NeCmp(e1, e2)())
        case _ => None
      }
      case terms.True => Some(TrueLit()())
      case t if newChunkBySnap.contains(t) =>
        val c = newChunkBySnap(t)
        val rcv = transformTerm(c._1.args.head)
        Some(FieldAccess(rcv.get, c._2.field)())
      case _ => None
    }
  }

  def transformState(s: State): Seq[Exp] = {

    val transformed = s.h.values.collect { case c: NonQuantifiedChunk => transformChunk(c) }.collect { case Some(e) => e }.toSeq
    transformed.filter {
      case _: FieldAccessPredicate => true
      case _ => false
    } ++ transformed.filter {
      case _: FieldAccessPredicate => false
      case _ => true
    }
  }

  def transformChunk(b: NonQuantifiedChunk): Option[Exp] = {

    b match {
      case bc: BasicChunk =>
        val rcv = transformTerm(bc.args.head)
        (bc, rcv) match {
          case (_, None) => None
          case (BasicChunk(FieldID, _, _, _, _, _, _), rcv) => Some(FieldAccessPredicate(FieldAccess(rcv.get, abductionUtils.getField(bc.id, s.program))(), transformTerm(b.perm).get)())
          case (BasicChunk(PredicateID, id, _, _, _, _, _), rcv) => Some(PredicateAccessPredicate(PredicateAccess(Seq(rcv.get), id.name)(), transformTerm(b.perm).get)())

        }
      case mwc: MagicWandChunk =>
        val rcvs = mwc.args.map(a => a -> transformTerm(a)).toMap
        if (rcvs.values.toSeq.contains(None)) None else {
          val shape = mwc.id.ghostFreeWand
          val expBindings = mwc.bindings.collect { case (lv, (term, _)) if rcvs.contains(term) => lv -> rcvs(term).get }
          val instantiated = shape.replace(expBindings)
          Some(instantiated)
          //Some(abductionUtils.getPredicate(s.program, rcv.get, transformTerm(b.perm).get))
        }
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

  def transformExp(e: Exp, strict: Boolean = true): Option[Exp] = {
    try {
      val res = e.transform {
        case FieldAccessPredicate(fa, perm) =>
          // We do not want to transform the entire field access, this would resolve the snap!
          val newRcv = transformExp(fa.rcv).get
          FieldAccessPredicate(FieldAccess(newRcv, fa.field)(), perm)()
        case fa@FieldAccess(target, field) =>

          // We do not get the guarantee that the chunks exist in the current state, so we can not evaluate them
          // directly
          safeEval(fa) match {
            // If the chunk exists in the current state, then we want to match the snap term
            case Some(term) =>
              val existingChunkTerm = transformTerm(term)
              existingChunkTerm match {
                case Some(nfa: FieldAccess) => nfa

                case Some(NullLit()) | Some(LocalVar(_, _)) | None =>
                  val rvcExp = transformExp(target)
                  FieldAccess(rvcExp.get, field)()

                // TODO nklose this wrong sometimes?
                // Specifically I think if we are transforming "in-place" then this is fine,
                // but if we are transforming "into the past" then this can be wrong because the
                // old value of the field is not necessarily equal to the new value

              }
            // Else we want to recurse and try to match the target
            case None =>
              val rvcExp = transformExp(target)
              FieldAccess(rvcExp.get, field)()
          }
        case lv: LocalVar => {
          val term: Term = s.g.values.getOrElse(lv, targetVars(lv))._1
          transformTerm(term).get
        }
      }
      Some(res)
    } catch {
      case _: NoSuchElementException => if (strict) None else Some(e)
    }
  }
}
