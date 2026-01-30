package viper.silicon.biabduction

import org.checkerframework.checker.units.qual.m
import viper.silicon.interfaces.state.NonQuantifiedChunk
import viper.silicon.resources.{FieldID, PredicateID}
import viper.silicon.rules.chunkSupporter.findChunk
import viper.silicon.state.terms.{BuiltinEquals, Null, Term, Var}
import viper.silicon.state._
import viper.silicon.state.terms.sorts.Perm
import viper.silicon.utils.ast.{BigAnd, BigOr}
import viper.silicon.verifier.Verifier
import viper.silver.ast
import viper.silver.ast.{AbstractLocalVar, Exp, Field, FieldAccess, FieldAccessPredicate, FractionalPerm, LocationAccess, PermExp, PredicateAccessPredicate}

import scala.annotation.tailrec
import scala.collection.immutable.TreeSeqMap

case class VarTransformer(s: State, v: Verifier, prefVars: Map[ast.AbstractLocalVar, (Term, Option[ast.Exp])],
                          targetHeap: Heap, newFieldChunks: Map[BasicChunk, ast.LocationAccess] = Map(),
                          otherVars: Map[ast.AbstractLocalVar, (Term, Option[ast.Exp])] = Map()) {

  //val pve: PartialVerificationError = Internal()

  // Ask the decider whether any of the terms are equal to a target.
  val matches: Map[Term, ast.Exp] = resolveMatches()

  val newChunkBySnap = newFieldChunks.map { case (c, fa: ast.FieldAccess) => c.snap -> (c, fa) }

  private def resolveMatches(): Map[Term, ast.Exp] = {

    val allTerms: Seq[Term] = (s.g.values.values.map { case (t1, _) => t1 }
      ++ s.h.values.collect {
      case c: BasicChunk if c.resourceID == FieldID => Seq(c.args.head, c.snap)
      case c: BasicChunk if c.resourceID == PredicateID => c.args
    }.flatten
      ++ prefVars.values.map(_._1) ++ otherVars.values.map(_._1)
      ++ v.decider.pcs.branchConditions.collect { case t => t.subterms.collect { case tVar: Var => tVar } }.flatten
    ).toSeq.distinct


    // The symbolic values of the target vars in the store. Everything else is an attempt to match things to these terms
    //val targetMap: Map[Term, AbstractLocalVar] = targets.view.map(localVar => s.g.get(localVar).get -> localVar).toMap
    val directPrefTargets = prefVars.map{case (lv, (t, _)) => t -> lv} //++ Map(terms.Null -> ast.NullLit()())

    val directTargets = directPrefTargets ++ otherVars.map{case (lv, (t, _)) => t -> lv}.filter { case (t, _) => !directPrefTargets.contains(t) }

    val directAliases = allTerms.map { t =>
      t -> directTargets.collectFirst { case (t1, e) if t.sort == t1.sort && v.decider.check(BuiltinEquals(t, t1), Verifier.config.checkTimeout()) => e }
    }.collect { case (t2, Some(e)) => t2 -> e }.toMap

    val chunksToResolve = targetHeap.values.collect { case c: BasicChunk
      if c.resourceID == FieldID && !(directAliases.contains(c.args.head) && directAliases.contains(c.snap)) && c.snap != Null => c
    }.toSeq

    resolveChunks(directAliases, chunksToResolve, allTerms.filter(!directAliases.contains(_)))
  }

  @tailrec
  private def resolveChunks(currentMatches: Map[Term, ast.Exp], remainingChunks: Seq[BasicChunk], remainingTerms: Seq[Term]): Map[Term, ast.Exp] = {
    remainingChunks.collectFirst { case c if currentMatches.contains(c.args.head) => c } match {
      case None => currentMatches
      case Some(c) =>
        val newExp = ast.FieldAccess(currentMatches(c.args.head), abductionUtils.getField(c.id, s.program))()
        val newMatches = currentMatches ++ remainingTerms.collect { case t if t.sort == c.snap.sort && v.decider.check(BuiltinEquals(t, c.snap), Verifier.config.checkTimeout()) => t -> newExp }
        resolveChunks(newMatches, remainingChunks.filter(_ != c), remainingTerms.filter(!newMatches.contains(_)))
    }
  }

  def permExpToTerm(permExp: Exp, v: Verifier): Option[Term] = {

    def binPermOp(e1: ast.Exp, e2: ast.Exp, op: (terms.Term, terms.Term) => terms.Term): Option[terms.Term] = {
      Some(op(
        permExpToTerm(e1, v).getOrElse(terms.FullPerm),
        permExpToTerm(e2, v).getOrElse(terms.FullPerm)
      ))
    }

    permExp match {
      case ast.IntLit(n) =>
        Some(terms.IntLiteral(n))
      case ast.FullPerm() =>
        Some(terms.FullPerm)
      case ast.NoPerm() =>
        Some(terms.NoPerm)
      case ast.WildcardPerm() =>
        val arp = v.decider.freshARP("abductionWC")
        v.decider.assume(arp._2, None, None)
        Some(arp._1)
      case ast.FractionalPerm(ast.IntLit(e1), ast.IntLit(e2)) =>
        Some(terms.FractionPerm((terms.IntLiteral(e1), terms.IntLiteral(e2))))
      case ast.PermMul(e1, e2) =>
        binPermOp(e1, e2, terms.PermTimes(_, _))
      case ast.PermSub(e1, e2) =>
        binPermOp(e1, e2, terms.PermMinus(_, _))
      case ast.PermAdd(e1, e2) =>
        binPermOp(e1, e2, terms.PermPlus(_, _))
      case ast.PermDiv(e1, e2) =>
        binPermOp(e1, e2, terms.PermIntDiv(_, _))
      case ast.PermPermDiv(e1, e2) =>
        binPermOp(e1, e2, terms.PermPermDiv(_, _))
      case _ => None
    }
  }

  // This function assumes that prefVars are the Vars in the precondition(s) and
  // targetHeap is the heap in the precondition(s)
  // prefVars: Map[ast.AbstractLocalVar, (Term, Option[ast.Exp])]
  /*def mergePreconditions(oldPres: Seq[Exp], newPres: Seq[Exp]): Seq[Exp] = {

    def resolveAlias(rcv: Exp): Option[Exp] =
      rcv match {
        case v: AbstractLocalVar =>
          prefVars
            .get(v)
            .flatMap { case (t, _) => matches.get(t) }
        case _ => None
      }

    val fapInNewPres: Set[(Exp, Field)] = newPres.collect {
        case FieldAccessPredicate(FieldAccess(rcv, field), _)  => (rcv, field)
      }.toSet

    val filteredOldPres =
      oldPres.filterNot {
        case FieldAccessPredicate(FieldAccess(rcvB, fieldB), _) =>
          resolveAlias(rcvB)
            .exists { aliasedRcv =>
              fapInNewPres.contains((aliasedRcv, fieldB))
            }
        case e =>
          false
      }



    val merged: Seq[Exp] = newPres ++ filteredOldPres
    merged
  }*/

  def transformTerm(t: Term): Option[ast.Exp] = {
    /*def binPermOp(t1: terms.Term, t2: terms.Term, op: (ast.Exp, ast.Exp) => ast.Exp): Option[ast.Exp] = {
      Some(op(
        transformTerm(t1).getOrElse(ast.FullPerm()()),
        transformTerm(t2).getOrElse(ast.FullPerm()())
      ))
    }*/

    def binPermOp(t1: terms.Term, t2: terms.Term, identity: ast.Exp, op: (ast.Exp, ast.Exp) => ast.Exp): Option[ast.Exp] = {
      val exp1 = transformTerm(t1).getOrElse(ast.FullPerm()())
      val exp2 = transformTerm(t2).getOrElse(ast.FullPerm()())

      (exp1, exp2) match {
        case (ast.WildcardPerm(), _) =>
          Some(ast.WildcardPerm()())
        case (_, ast.WildcardPerm()) =>
          Some(ast.WildcardPerm()())
        case _ =>
          Some(op(exp1, exp2))
      }
    }

    t match {
      case t if matches.contains(t) => matches.get(t)
      case BuiltinEquals(t1, t2) => (transformTerm(t1), transformTerm(t2)) match {
        case (Some(e1), Some(e2)) =>
          Some(ast.EqCmp(e1, e2)())
        case _ => None
      }
      case v@terms.Var(_) if v.isWildcard => Some(ast.WildcardPerm()())
      // FIXME: This is probably wrong
      case terms.PermMin(t1, t2) =>
        val e1 = transformTerm(t1).getOrElse(ast.FullPerm()())
        val e2 = transformTerm(t2).getOrElse(ast.FullPerm()())
        val minP = abductionUtils.permMin(e1, e2)
        Some(ast.FractionalPerm(ast.IntLit(minP.numerator)(), ast.IntLit(minP.denominator)())())

      case terms.FractionPermLiteral(r) => Some(ast.FractionalPerm(ast.IntLit(r.numerator)(), ast.IntLit(r.denominator)())())
      case terms.FullPerm => Some(ast.FullPerm()())
      case terms.NoPerm => Some(ast.NoPerm()())
      case terms.PermTimes(t1, t2) => binPermOp(t1, t2, ast.FullPerm()(), ast.PermMul(_, _)())
      // Div is just TIMES 1 / n
      // case terms.PermDiv(t1, t2) => binPermOp(t1, t2, ast.PermDiv(_, _)())
      case terms.PermPermDiv(t1, t2) => binPermOp(t1, t2, ast.FullPerm()(), ast.PermPermDiv(_, _)())
      case terms.FractionPerm(t1, t2) => binPermOp(t1, t2, ast.FullPerm()(), ast.PermDiv(_, _)())
      case terms.PermMinus(t1, t2) => binPermOp(t1, t2, ast.NoPerm()(), ast.PermSub(_, _)())
      case terms.PermPlus(t1, t2) => binPermOp(t1, t2, ast.NoPerm()(), ast.PermAdd(_, _)())
      case terms.Null => Some(ast.NullLit()())
      case terms.Not(t1) => transformTerm(t1).flatMap(e1 => Some(ast.Not(e1)()))
      case terms.Not(BuiltinEquals(t1, t2)) => (transformTerm(t1), transformTerm(t2)) match {
        case (Some(e1), Some(e2)) => Some(ast.NeCmp(e1, e2)())
        case _ => None
      }
      case terms.True => Some(ast.TrueLit()())
      case t if newChunkBySnap.contains(t) =>
        val c = newChunkBySnap(t)
        val rcv = transformTerm(c._1.args.head)
        Some(ast.FieldAccess(rcv.get, c._2.field)())
      case and: terms.And =>
        val subs = and.ts.map(transformTerm)
        if (subs.contains(None)) None else Some(BigAnd(subs.map(_.get)))
      case or: terms.Or =>
        val subs = or.ts.map(transformTerm)
        if (subs.contains(None)) None else Some(BigOr(subs.map(_.get)))
      /*
      case app: terms.App =>
        app.applicable match {
          case df: terms.DomainFun => 
            val args = app.args.map(transformTerm)
            if (args.contains(None)) None else {
              val funcName = df.id.name.split('[').head
              val domFunc = s.program.domainFunctionsByName.get(funcName)
              Some(ast.DomainFuncApp(domFunc.get, args.map(_.get), Map())())
            }
            
          case _ => 
            val args = app.args.tail.map(transformTerm)
            if (args.contains(None)) None else {
              val funcName = app.applicable.id.name
              val func = s.program.functionsByName.get(funcName)
              Some(ast.FuncApp(func.get, args.map(_.get))())
            }
        }
        */
      case sl: terms.SeqLength => transformTerm(sl.p).flatMap(e => Some(ast.SeqLength(e)()))
      case sa: terms.SeqAt => (transformTerm(sa.p0), transformTerm(sa.p1)) match {
        case (Some(e0), Some(e1)) => Some(ast.SeqIndex(e0, e1)())
        case _ => None
      }
      case terms.IntLiteral(n) => Some(ast.IntLit(n)())
      case _ => None
    }
  }

  def transformState(s: State): Seq[ast.Exp] = {

    val transformed = s.h.values.collect { case c: NonQuantifiedChunk => transformChunk(c) }.collect { case Some(e) => e }.toSeq
    transformed.filter {
      case _: ast.FieldAccessPredicate => true
      case _ => false
    } ++ transformed.filter {
      case _: ast.FieldAccessPredicate => false
      case _ => true
    }
  }

  def transformChunk(b: NonQuantifiedChunk): Option[ast.Exp] = {

    b match {
      case bc: BasicChunk =>
        val rcv = transformTerm(bc.args.head)
        (bc, rcv) match {
          case (_, None) => None
          case (BasicChunk(FieldID, _, _, _, _, _, _, _), rcv) => Some(ast.FieldAccessPredicate(ast.FieldAccess(rcv.get, abductionUtils.getField(bc.id, s.program))(), Some(transformTerm(b.perm).get))())
          case (BasicChunk(PredicateID, id, _, _, _, _, _, _), rcv) => Some(ast.PredicateAccessPredicate(ast.PredicateAccess(Seq(rcv.get), id.name)(), Some(transformTerm(b.perm).get))())

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

  private def safeEval(e: ast.Exp): Option[Term] = {
    e match {
      case lv: ast.LocalVar => Some(s.g(lv))
      case fa@ast.FieldAccess(target, _) =>
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

  def transformExp(e: ast.Exp, strict: Boolean = true): Option[ast.Exp] = {
    try {
      val res = e.transform {
        
        // We do not want to resolve things to fields accesses for wands, as that would not be self-framing 
        case ast.MagicWand(left: ast.AbstractLocalVar, right: ast.AbstractLocalVar) =>
          val leftT = s.g.values(left)._1
          val rightT = s.g.values(right)._1
          val directPrefTargets = prefVars.map{case (lv, (t, _)) => t -> lv}
          val otherTargets = otherVars.map{case (lv, (t, _)) => t -> lv}
          val leftE = directPrefTargets.get(leftT).orElse(otherTargets.get(leftT)).get
          val rightE = directPrefTargets.get(rightT).orElse(otherTargets.get(rightT)).get
          ast.MagicWand(leftE, rightE)()
        
        case ast.FieldAccessPredicate(fa, perm) =>
          // We do not want to transform the entire field access, this would resolve the snap!
          val newRcv = transformExp(fa.rcv).get
          ast.FieldAccessPredicate(ast.FieldAccess(newRcv, fa.field)(), perm)()
        case fa@ast.FieldAccess(target, field) =>

          // We do not get the guarantee that the chunks exist in the current state, so we can not evaluate them
          // directly
          safeEval(fa) match {
            // If the chunk exists in the current state, then we want to match the snap term
            case Some(term) =>
              val existingChunkTerm = transformTerm(term)
              existingChunkTerm match {
                case Some(nfa: ast.FieldAccess) => nfa

                case Some(ast.NullLit()) | Some(ast.LocalVar(_, _)) | None =>
                  val rvcExp = transformExp(target)
                  ast.FieldAccess(rvcExp.get, field)()

                // TODO nklose this wrong sometimes?
                // Specifically I think if we are transforming "in-place" then this is fine,
                // but if we are transforming "into the past" then this can be wrong because the
                // old value of the field is not necessarily equal to the new value

              }
            // Else we want to recurse and try to match the target
            case None =>
              val rvcExp = transformExp(target)
              ast.FieldAccess(rvcExp.get, field)()
          }
        case lv: ast.LocalVar => {
          val term: Term = s.g.values.getOrElse(lv, (prefVars ++ otherVars)(lv))._1
          if(strict){
            transformTerm(term).get
          } else {
            transformTerm(term).getOrElse(lv)
          }
        }
      }
      println(s"Transformed $e in $res")
      Some(res)
    } catch {
      case _: NoSuchElementException => if (strict) None else Some(e)
    }
  }
}
