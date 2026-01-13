package viper.silicon.biabduction

import viper.silicon.interfaces.{NonFatalResult, Success, VerificationResult}
import viper.silicon.rules.chunkSupporter.findChunk
import viper.silicon.rules.evaluator
import viper.silicon.state.terms.Term
import viper.silicon.state._
import viper.silicon.verifier.Verifier
import viper.silver.ast._
import viper.silver.verifier.PartialVerificationError

import scala.annotation.tailrec

object abductionUtils {

  def isValidPredicate(pred: Predicate): Boolean = {
    pred.formalArgs.size == 1 && pred.body.isDefined
  }

  def getVars(t: Term, g: Store): Seq[AbstractLocalVar] = {
    g.values.collect({ case (v, (t1, _)) if t1 == t => v }).toSeq
  }

  def getField(name: BasicChunkIdentifier, p: Program): Field = {
    p.fields.find(_.name == name.name).get
  }

  def getPredicate(name: BasicChunkIdentifier, p: Program): Predicate = {
    p.predicates.find(_.name == name.name).get
  }

  def getAbductionSuccesses(vr: NonFatalResult): Seq[AbductionSuccess] = {
    (vr +: vr.previous).collect { case Success(Some(abd: AbductionSuccess)) => abd }
  }

  def getAbductionFailures(vr: NonFatalResult): Seq[BiAbductionFailure] = {
    (vr +: vr.previous).collect { case Success(Some(abd: BiAbductionFailure)) => abd }
  }

  def getFramingSuccesses(vr: NonFatalResult): Seq[FramingSuccess] = {
    (vr +: vr.previous).collect { case Success(Some(framing: FramingSuccess)) => framing }
  }

  def getInvariantSuccesses(vr: NonFatalResult): Seq[LoopInvariantSuccess] = {
    (vr +: vr.previous).collect { case Success(Some(inv: LoopInvariantSuccess)) => inv }
  }

  def getBiAbductionSuccesses(vr: NonFatalResult): Seq[BiAbductionSuccess] = {
    (vr +: vr.previous).collect { case Success(Some(suc: BiAbductionSuccess)) => suc }
  }

  def getContainingPredicates(f: FieldAccess, p: Program): Seq[Predicate] = {

    p.predicates.filter { pred =>
      val absAcc = f.copy(rcv = pred.formalArgs.head.localVar)(f.pos, f.info, f.errT)
      pred.body.isDefined && pred.body.get.contains(absAcc)
    }
  }

  def checkBc(v: Verifier, bc: Term, ignoredBcs: Seq[Term]): Boolean = {
    v.decider.check(terms.Implies(terms.And(ignoredBcs), bc), Verifier.config.checkTimeout())
  }

  val dummyEndStmt: Stmt = Label("Dummy End of method statement", Seq())()

  private val dummyLoopEndName = "Dummy End of loop statement"

  def getEndOfLoopStmt(loop: While): Label = Label(dummyLoopEndName, Seq(loop.cond))()

  def isEndOfLoopStmt(stmt: Stmt): Boolean = stmt match {
    case Label(name, _) if name == dummyLoopEndName => true
    case _ => false
  }

  def getWhile(condition: Exp, method: Method): While = {
    method.body.get.toSeq.collectFirst {
      case w: While if w.cond.pos == condition.pos => w
    }.get
  }

  @tailrec
  def joinBcsTerms[T](bcs: Seq[(Seq[T], Seq[Term])]): Seq[(Seq[T], Seq[Term])] = {
    bcs.combinations(2).collectFirst {
      case Seq((a_res, a_pcs), (b_res, b_pcs)) if canJoinTerms(a_pcs, b_pcs).isDefined => Seq((a_res, a_pcs), (b_res, b_pcs))
    } match {
      case Some(Seq((a_res, a_pcs), (b_res, b_pcs))) =>
        val rest = bcs.filter { case (c_res, _) => c_res != a_res && c_res != b_res }
        val joined = canJoinTerms(a_pcs, b_pcs).get
        joinBcsTerms(rest :+ (a_res ++ b_res, joined))
      case None => bcs
    }
  }

  private def canJoinTerms(a: Seq[Term], b: Seq[Term]): Option[Seq[Term]] = {
    (a.diff(b), b.diff(a)) match {
      case (Seq(eq), Seq(terms.Not(t))) if eq == t => Some(a.filter(_ != eq))
      case (Seq(terms.Not(t)), Seq(eq)) if eq == t => Some(b.filter(_ != eq))
      case (Seq(), _) => Some(a)
      case (_, Seq()) => Some(b)
      case _ => None
    }
  }

  @tailrec
  def joinBcsExps[T](bcs: Seq[(Seq[T], Seq[Exp])]): Seq[(Seq[T], Seq[Exp])] = {
    bcs.combinations(2).collectFirst {
      case Seq((a_res, a_pcs), (b_res, b_pcs)) if canJoinExps(a_pcs, b_pcs).isDefined => Seq((a_res, a_pcs), (b_res, b_pcs))
    } match {
      case Some(Seq((a_res, a_pcs), (b_res, b_pcs))) =>
        val rest = bcs.filter { case (c_res, _) => c_res != a_res && c_res != b_res }
        val joined = canJoinExps(a_pcs, b_pcs).get
        joinBcsExps(rest :+ (a_res ++ b_res, joined))
      case None => bcs
    }
  }

  private def canJoinExps(a: Seq[Exp], b: Seq[Exp]): Option[Seq[Exp]] = {
    (a.diff(b), b.diff(a)) match {
      case (Seq(eq), Seq(Not(t))) if eq == t => Some(a.filter(_ != eq))
      case (Seq(Not(t)), Seq(eq)) if eq == t => Some(b.filter(_ != eq))
      case (Seq(), _) => Some(a)
      case (_, Seq()) => Some(b)
      case _ => None
    }
  }

  def findChunkFromExp(loc: LocationAccess, s: State, v: Verifier, pve: PartialVerificationError)(Q: Option[BasicChunk] => VerificationResult): VerificationResult = {

    val arg = loc match {
      case FieldAccess(rcv, _) => rcv
      case PredicateAccess(args, _) => args.head
    }
    // TODO this can fail for field access args that don't exist
    evaluator.eval(s, arg, pve, v) { (s2, term, _, v2) =>
      val resource = loc.res(s2.program)
      val id = ChunkIdentifier(resource, s2.program)
      val chunk = findChunk[BasicChunk](s2.h.values, id, Seq(term), v2)
      Q(chunk)
    }
  }

  def findChunks(locs: Seq[LocationAccess], s: State, v: Verifier, pve: PartialVerificationError)(Q: Map[BasicChunk, LocationAccess] => VerificationResult): VerificationResult = {
    locs match {
      case Seq() => Q(Map())
      case loc +: rest =>
        findChunkFromExp(loc, s, v, pve) {
          case Some(chunk) => findChunks(rest, s, v, pve) { chunks => Q(chunks + (chunk -> loc)) }
        }
    }
  }

  def findOptChunks(locs: Seq[LocationAccess], s: State, v: Verifier, pve: PartialVerificationError)(Q: Map[BasicChunk, LocationAccess] => VerificationResult): VerificationResult = {
    locs match {
      case Seq() => Q(Map())
      case loc +: rest =>
        findChunkFromExp(loc, s, v, pve) {
          case Some(chunk) => findOptChunks(rest, s, v, pve) { chunks => Q(chunks + (chunk -> loc)) }
          case None => findOptChunks(rest, s, v, pve) { Q }
        }
    }
  }

  // We need to sort exps before producing them because we have to create fields before creating stuff on the fields
  // The idea is that the length of something on the field will always be greater than the field itself.
  def sortExps(exps: Seq[Exp]): Seq[Exp] = {
    val fields = exps.collect {
      case f: FieldAccessPredicate => f
      case impF@Implies(_, _: FieldAccessPredicate) => impF
    }.sortBy(e => e.size)
    val preds = exps.collect {
      case p: PredicateAccessPredicate => p
      case impP@Implies(_, _: PredicateAccessPredicate) => impP
    }
    val others = exps.diff(fields ++ preds)
    fields ++ preds ++ others
  }

}
