package viper.silicon.biabduction

import viper.silicon.decider.PathConditionStack
import viper.silicon.interfaces._
import viper.silicon.interfaces.state.Chunk
import viper.silicon.interfaces.state.NonQuantifiedChunk
import viper.silicon.rules.{executionFlowController, executor, producer}
import viper.silicon.state._
import viper.silicon.state.terms.Term
import viper.silicon.utils.ast.BigAnd
import viper.silicon.utils.freshSnap
import viper.silicon.verifier.Verifier
import viper.silver.ast._
import viper.silver.verifier.errors.Internal
import viper.silver.verifier.reasons.{InsufficientPermission, MagicWandChunkNotFound}
import viper.silver.verifier.{DummyReason, PartialVerificationError, VerificationError}

trait BiAbductionResult {
  def s: State
  def v: Verifier
}

trait BiAbductionSuccess extends BiAbductionResult {
  def addToMethod(m: Method): Option[Method]
}

// TODO nklose BiAbductionSuccess should be able to provide arbitrary transformations of methods. Then we can just
// use this for all cases and need less dummy stuff

case class AbductionSuccess(s: State, v: Verifier, pcs: Seq[PathConditionStack], state: Seq[Exp] = Seq(), stmts: Seq[Stmt] = Seq(), trigger: Option[Positioned] = None) extends BiAbductionSuccess {

  def addToMethod(m: Method): Option[Method] = {
    val ins = m.formalArgs.map(_.localVar)
    val preHeap = s.oldHeaps.head._2
    val inVars = s.g.values.collect { case (v, t) if ins.contains(v) => (v, t) }
    val pres = toPrecondition(inVars, preHeap)
    pres.map{ somePres =>

      val body = m.body.get
      val newBody: Seqn = trigger match {
        case None => body
        case Some(t: Stmt) if t == abductionUtils.dummyEndStmt => Seqn(body.ss ++ stmts, body.scopedSeqnDeclarations)(body.pos, body.info, body.errT)
        case Some(t: Stmt) if abductionUtils.isEndOfLoopStmt(t) =>
          val loop = abductionUtils.getWhile(t.asInstanceOf[Label].invs.head, m)
          val newLoopBody = loop.body.copy(ss = loop.body.ss ++ stmts)(pos = loop.body.pos, info = loop.body.info, errT = loop.body.errT)
          val newLoop = loop.copy(body = newLoopBody)(loop.pos, loop.info, loop.errT)
          body.transform { case stmt if stmt == loop => newLoop}
        case Some(t: Stmt) => body.transform {
          case stmt if stmt == t => Seqn(stmts :+ t, Seq())(t.pos, t.info, t.errT)
        }
        case Some(e: Exp) => body.transform {
          case ifStmt: If if ifStmt.cond == e => Seqn(stmts :+ ifStmt, Seq())(ifStmt.pos, ifStmt.info, ifStmt.errT)
          case whileStmt: While if whileStmt.cond == e => Seqn(stmts :+ whileStmt, Seq())(whileStmt.pos, whileStmt.info, whileStmt.errT)
        }
      }
      m.copy(pres = m.pres ++ somePres, body = Some(newBody))(pos = m.pos, info = m.info, errT = m.errT)

    }
  }

  override def toString: String = {
    "Abduced pres " + state.length + ", Abduced statements " + stmts.length
  }

  def toPrecondition(preVars: Map[AbstractLocalVar, (Term, Option[Exp])], preHeap: Heap, ignoredBcs: Seq[Term] = Seq()): Option[Seq[Exp]] = {

    val pres = pcs.map { pc =>

      // We have to use the pcs from the abduction point
      val prevPcs = v.decider.pcs
      v.decider.setPcs(pc)
      val varTrans = VarTransformer(s, v, preVars, preHeap)
      val presTransformed = state.map { pre =>
        varTrans.transformExp(pre)
      }

      if (presTransformed.contains(None)) {
        None // We could not express the state as a precondition
      } else {
        val bcs = v.decider.pcs.branchConditions.collect {
          case bc if !abductionUtils.checkBc(v, bc, ignoredBcs) => varTrans.transformTerm(bc)
        }.collect { case Some(e) if
          e != TrueLit()() => varTrans.transformExp(e).get
        }.toSet

        val presFinal = presTransformed.map { e =>
          if (bcs.isEmpty) {
            e.get
          } else {
            Implies(BigAnd(bcs), e.get)()
          }
        }
        v.decider.setPcs(prevPcs)
        Some(presFinal)
      }
    }
    if(pres.contains(None)){
      None
    } else {
      // TODO nklose we maybe want to combine stuff here
      Some(pres.flatMap(_.get).distinct)
    }
  }
}

case class LoopInvariantSuccess(s: State, v: Verifier, invs: Seq[Exp] = Seq(), loop: While) extends BiAbductionSuccess {
  override def toString: String = "Successful loop invariant abduction"

  def addToMethod(m: Method): Option[Method] = {
    val body = m.body.get
    val newBody = body.transform {
      case l: While if l.cond == loop.cond =>
        l.copy(invs = l.invs ++ invs)(pos = l.pos, info = l.info, errT = l.errT)
      case other => other
    }
    Some(m.copy(body = Some(newBody))(pos = m.pos, info = m.info, errT = m.errT))
  }
}

case class FramingSuccess(s: State, v: Verifier, posts: Seq[Exp], loc: Position) extends BiAbductionSuccess {
  override def toString: String = "Successful framing"

  def addToMethod(m: Method): Option[Method] = {
    Some(m.copy(posts = m.posts ++ posts)(pos = m.pos, info = m.info, errT = m.errT))
  }
}

case class BiAbductionFailure(s: State, v: Verifier) extends BiAbductionResult {
  override def toString: String = "Abduction failed"
}

trait RuleApplier[S] {

  protected val rules: Seq[BiAbductionRule[S]]

  /**
    * Recursively applies the rules until we reach the end of the rules list.
    */
  def applyRules(in: S, currentRule: Int = 0)(Q: S => VerificationResult): VerificationResult = {

    if (currentRule == rules.length) {
      Q(in)
    } else {
      rules(currentRule).apply(in) {
        case Some(out) =>
          applyRules(out)(Q)
        case None =>
          applyRules(in, currentRule + 1)(Q)
      }
    }
  }
}

trait BiAbductionRule[S] {

  val pve: PartialVerificationError = Internal()
  val ve: VerificationError = pve.dueTo(DummyReason)

  def apply(q: S)(Q: Option[S] => VerificationResult): VerificationResult

}

object BiAbductionSolver {

  def solveAbduction(s: State, v: Verifier, f: Failure, trigger: Option[Positioned] = None)(Q: (State, AbductionSuccess, Verifier) => VerificationResult): VerificationResult = {

    val reason = f.message.reason match {
      case reason: InsufficientPermission =>
        val acc = reason.offendingNode match {
          case n: FieldAccess => FieldAccessPredicate(n, FullPerm()())()
          case n: PredicateAccess => PredicateAccessPredicate(n, FullPerm()())()
        }
        Some(acc)
      case reason: MagicWandChunkNotFound => Some(reason.offendingNode)
      case _ => None
    }
    reason match {
      case None => f
      case Some(abdGoal) =>

        val tra = f.message.failureContexts.collectFirst {
          case SiliconAbductionFailureContext(trafo) if trafo.isDefined => trafo.get
        }

        val reses = executionFlowController.locally(s, v) { (s1, v1) =>
          val qPre = AbductionQuestion(s1, v1, Seq(abdGoal), trigger=trigger)
          val q = tra match {
            case Some(trafo) => trafo.f(qPre).asInstanceOf[AbductionQuestion]
            case _ => qPre
          }
          AbductionApplier.applyRules(q){
            q1 =>
              if (q1.goal.isEmpty) {
                Success(Some(AbductionSuccess(q1.s, q1.v, Seq(q1.v.decider.pcs.duplicate()), q1.foundState, q1.foundStmts, trigger)))
              } else {
                f
              }
          }
        }
        reses match {
          case f: FatalResult => f
          case nf: NonFatalResult =>
            abductionUtils.getAbductionSuccesses(nf) match {
              case Seq(abd) =>
                producer.produces(s, freshSnap, abd.state.reverse, _ => Internal(), v) {
                  (s2, v2) =>
                    executor.execs(s2, abd.stmts, v2) {
                      (s3, v3) =>
                        Q(s3, abd.copy(s = s3, v = v3), v3)
                    }
                }
              case Seq(a, b) if a.state == b.state && a.stmts == b.stmts =>
                producer.produces(s, freshSnap, a.state.reverse, _ => Internal(), v) {
                  (s2, v2) =>
                    executor.execs(s2, a.stmts, v2) {
                      (s3, v3) =>
                        Q(s3, a.copy(s = s3, v = v3, pcs = a.pcs ++ b.pcs), v3)
                    }
                }
            }
        }
    }
  }


  def solveAbstraction(s: State, v: Verifier, ignoredBcs: Seq[Term] = Seq(), fixedChunks: Seq[Chunk] = Seq())(Q: (State, Seq[Exp], Verifier) => VerificationResult): VerificationResult = {
    val q = AbstractionQuestion(s, v, fixedChunks)
    AbstractionApplier.applyRules(q) { q1 =>
      Success(Some(solveFraming(q1.s, q1.v, q1.s.g.values, ignoredBcs = ignoredBcs)))
    } match {
      case res: NonFatalResult =>
        val exps = abductionUtils.getFramingSuccesses(res).head
        Q(exps.s, exps.posts, exps.v)
    }
  }

  // This does not do abstraction, but just transforms state back into expressions.
  def solveFraming(s: State, v: Verifier, postVars: Map[AbstractLocalVar, (Term, Option[Exp])], loc: Position = NoPosition, ignoredBcs: Seq[Term] = Seq()): FramingSuccess = {

    val tra = VarTransformer(s, v, postVars, s.h)
    val res = s.h.values.collect { case c: NonQuantifiedChunk => tra.transformChunk(c) }.collect { case Some(e) => e }.toSeq
    val bcs = v.decider.pcs.branchConditions
      .collect { case term: Term if !abductionUtils.checkBc(v, term, ignoredBcs) => tra.transformTerm(term) }
      .collect { case Some(e) if e != TrueLit()() => e }.toSet
    val posts = res.map { e =>
      if (bcs.isEmpty) {
        e
      } else {
        Implies(BigAnd(bcs), e)()
      }
    }
    FramingSuccess(s, v, posts = posts, loc)
  }
}

object abductionUtils {

  def isValidPredicate(pred: Predicate): Boolean = {
    pred.formalArgs.size == 1 && (pred.body match {
      case None => false
      case Some(body) =>
        !body.topLevelConjuncts.exists {
          case _: FieldAccessPredicate => false
          case _: Implies => false
          case _ => true
        }
    })
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

    p.predicates.filter{ pred =>
      val absAcc = f.copy(rcv = pred.formalArgs.head.localVar)(f.pos, f.info, f.errT)
      pred.body.get.contains(absAcc)
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
      case w: While if w.cond == condition => w
    }.get
  }
}
