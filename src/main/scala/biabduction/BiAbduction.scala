package viper.silicon.biabduction

import viper.silicon.decider.PathConditionStack
import viper.silicon.interfaces._
import viper.silicon.interfaces.state.Chunk
import viper.silicon.interfaces.state.NonQuantifiedChunk
import viper.silicon.rules.consumer.consumes
import viper.silicon.rules.{executionFlowController, executor, producer}
import viper.silicon.state._
import viper.silicon.state.terms.Term
import viper.silicon.utils.ast.BigAnd
import viper.silicon.utils.freshSnap
import viper.silicon.verifier.Verifier
import viper.silver.ast._
import viper.silver.verifier.errors.{Internal, PostconditionViolated}
import viper.silver.verifier.reasons.{InsufficientPermission, MagicWandChunkNotFound}
import viper.silver.verifier.{DummyReason, PartialVerificationError, VerificationError}

trait BiAbductionResult {
  def s: State

  def v: Verifier
}

trait BiAbductionSuccess extends BiAbductionResult

// TODO nklose BiAbductionSuccess should be able to provide arbitrary transformations of methods. Then we can just
// use this for all cases and need less dummy stuff

case class AbductionSuccess(s: State, v: Verifier, pcs: Seq[PathConditionStack], state: Seq[Exp] = Seq(), stmts: Seq[Stmt] = Seq(), trigger: Option[Positioned] = None) extends BiAbductionSuccess {

  private def bcsExps(pc: PathConditionStack, ignoredBcs: Seq[Term]): Set[Exp] = {
    val prevPcs = v.decider.pcs
    v.decider.setPcs(pc)
    val varTrans = VarTransformer(s, v, s.g.values, s.h)
    val bcTerms = v.decider.pcs.branchConditions
    val bcExpOpt = bcTerms.collect {
     case bc if !ignoredBcs.contains(bc) => varTrans.transformTerm(bc)
    }
    val bcExp = bcExpOpt.collect { case Some(e) => e }.toSet
    v.decider.setPcs(prevPcs)
    bcExp
  }

  def addToMethod(m: Method): Option[Method] = {
    val ins = m.formalArgs.map(_.localVar)
    val preHeap = s.oldHeaps.head._2
    val inVars = s.g.values.collect { case (v, t) if ins.contains(v) => (v, t) }
    val pres = toPrecondition(inVars, preHeap)
    pres.map { somePres =>

      val body = m.body.get
      val newBody: Seqn = trigger match {
        case None => body
        case Some(t: Stmt) if t == abductionUtils.dummyEndStmt => Seqn(body.ss ++ stmts, body.scopedSeqnDeclarations)(body.pos, body.info, body.errT)
        case Some(t: Stmt) if abductionUtils.isEndOfLoopStmt(t) =>
          val loop = abductionUtils.getWhile(t.asInstanceOf[Label].invs.head, m)
          val newLoopBody = loop.body.copy(ss = loop.body.ss ++ stmts)(pos = loop.body.pos, info = loop.body.info, errT = loop.body.errT)
          val newLoop = loop.copy(body = newLoopBody)(loop.pos, loop.info, loop.errT)
          body.transform { case stmt if stmt == loop => newLoop }
        case Some(t: Stmt) =>
          body.transform {
            case stmt if stmt == t =>
              Seqn(stmts :+ t, Seq())(t.pos, t.info, t.errT)
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

        val bcs = bcsExps(pc, ignoredBcs).map { exp => varTrans.transformExp(exp) }.collect { case Some(e)  => e }
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
    if (pres.contains(None)) {
      None
    } else {
      // TODO nklose we maybe want to combine stuff here
      Some(pres.flatMap(_.get).distinct)
    }
  }
}

case class LoopInvariantSuccess(s: State, v: Verifier, invs: Seq[Exp] = Seq(), loop: While) extends BiAbductionSuccess {
  override def toString: String = "Successful loop invariant abduction"

  def addToMethod(m: Method): Method = {
    val body = m.body.get
    val newBody = body.transform {
      case l: While if l.cond == loop.cond =>
        l.copy(invs = l.invs ++ invs)(pos = l.pos, info = l.info, errT = l.errT)
      case other => other
    }
    m.copy(body = Some(newBody))(pos = m.pos, info = m.info, errT = m.errT)
  }
}

case class FramingSuccess(s: State, v: Verifier, posts: Seq[Exp], stmts: Seq[Stmt], loc: Positioned, pcs: PathConditionStack, conds: Seq[Exp]) extends BiAbductionSuccess {
  override def toString: String = "Successful framing"

  def addToMethod(m: Method): Method = {
    /*val (newPost, stmt) = if (conds.isEmpty) {
      (BigAnd(posts), Seqn(stmts, Seq())())
    } else {
      (Implies(BigAnd(conds), BigAnd(posts))(), If(BigAnd(conds), Seqn(stmts, Seq())(), Seqn(Seq(), Seq())())())
    }*/
    val body = m.body.get
    val newBody = body.copy(ss = body.ss :+ Seqn(stmts, Seq())())(pos = body.pos, info = body.info, errT = body.errT)
    m.copy(posts = m.posts ++ posts, body = Some(newBody))(pos = m.pos, info = m.info, errT = m.errT)
  }
}

case class BiAbductionFailure(s: State, v: Verifier, pcs: PathConditionStack) extends BiAbductionResult {
  override def toString: String = "Abduction failed"

  def addToMethod(m: Method): Method = {
    val ins = m.formalArgs.map(_.localVar)
    val preHeap = s.oldHeaps.head._2
    val inVars = s.g.values.collect { case (v, t) if ins.contains(v) => (v, t) }
    val prevPcs = v.decider.pcs
    v.decider.setPcs(pcs)
    val varTrans = VarTransformer(s, v, inVars, preHeap)
    val bcTerms = v.decider.pcs.branchConditions
    val bcExpOpt = bcTerms.map {
      bc => varTrans.transformTerm(bc)
    }
    v.decider.setPcs(prevPcs)

    val bcExp = bcExpOpt.collect { case Some(e) => e }.toSet
    if (bcExp.nonEmpty) {
      val pre = Not(BigAnd(bcExp))()
      m.copy(pres = m.pres :+ pre)(pos = m.pos, info = m.info, errT = m.errT)
    }
    else {
      m
    }

  }
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

    val initPcs = v.decider.pcs.duplicate()
    //val initTra = VarTransformer(s, v, s.g.values, s.h)

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
          val qPre = AbductionQuestion(s1, v1, Seq(abdGoal), trigger = trigger)
          val q = tra match {
            case Some(trafo) => trafo.f(qPre).asInstanceOf[AbductionQuestion]
            case _ => qPre
          }
          AbductionApplier.applyRules(q) {
            q1 =>
              if (q1.goal.isEmpty) {
                Success(Some(AbductionSuccess(q1.s, q1.v, Seq(q1.v.decider.pcs.duplicate()), q1.foundState.reverse, q1.foundStmts.reverse, trigger)))
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
                producer.produces(s, freshSnap, abd.state, _ => Internal(), v) {
                  (s2, v2) =>
                    executor.execs(s2, abd.stmts, v2) {
                      (s3, v3) =>
                        if (v3.decider.checkSmoke()) {
                          // TODO nklose this result still receives the branch conditions as an implication, which is nonsense
                          // Easy fix: 
                          // val conds = initPcs.branchConditions.map(initTra.transformTerm).collect({case Some(e) => e})
                          Success(Some(BiAbductionFailure(s, v, initPcs)))
                        } else {
                          Q(s3, abd.copy(s = s3, v = v3), v3)
                        }
                    }
                }
              case Seq(a, b) if a.state == b.state && a.stmts == b.stmts =>
                producer.produces(s, freshSnap, a.state, _ => Internal(), v) {
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

  def solveAbstraction(s: State, v: Verifier, fixedChunks: Seq[Chunk] = Seq())(Q: (State, Seq[Exp], Verifier) => VerificationResult): VerificationResult = {
    val q = AbstractionQuestion(s, v, fixedChunks)
    AbstractionApplier.applyRules(q) { q1 =>
      val tra = VarTransformer(q1.s, q1.v, q1.s.g.values, q1.s.h)
      val res = q1.s.h.values.collect { case c: NonQuantifiedChunk => tra.transformChunk(c) }.collect { case Some(e) => e }.toSeq
      Q(q1.s, res, q1.v)
    }
  }

  def solveFraming(s: State, v: Verifier, pvef: Exp => PartialVerificationError, tra: VarTransformer, loc: Positioned, knownPosts: Seq[Exp])(Q: FramingSuccess => VerificationResult): VerificationResult = {

    //val tra = VarTransformer(s, v, targetVars, s.h)
    executionFlowController.tryOrElse1[Term](s, v) { (s, v, QS) =>
      consumes(s, knownPosts, pvef, v)(QS)
    } { (s1: State, _: Term, v1: Verifier) =>
      executionFlowController.locallyWithResult[Seq[Exp]](s1, v1) { (s1a, v1a, T) =>
        BiAbductionSolver.solveAbstraction(s1a, v1a) { (s2, framedPosts, v2) =>
          val newPosts = framedPosts.map { e => tra.transformExp(e) }.collect { case Some(e) => e }
          T(newPosts)
        }
      } {
        // We consumed all the posts and did not find any new ones. So create a fresh Framing Success with the bcs
        case Seq() =>
          val bcsExps = v.decider.pcs.branchConditions
            .map { bc => tra.transformTerm(bc) }
          .collect{ case Some(e) => e} // TODO we currently just discard bcs we cannot transform. Is this always right?
          Q(FramingSuccess(s1, v1, Seq(), Seq(), loc, v.decider.pcs.duplicate(), bcsExps)) // No new state or needed stmts
        // We consumed the post conditions and found new ones. Handle the new ones and add them to the result
        case newPosts1 =>
          solveFraming(s1, v1, pvef, tra, loc, newPosts1) { frame =>
            val newFrame = frame.copy(posts = frame.posts ++ newPosts1)
            Q(newFrame)
          }
      }
    } {
      // We failed to fulfill the posts. Perform abduction, add the results and try again.
      f =>
        BiAbductionSolver.solveAbduction(s, v, f, Some(loc))((s3, res, v3) => {
          solveFraming(s3, v3, pvef, tra, loc, knownPosts) {
            frame =>
              val newAbdRes = if (res.state.nonEmpty) {
                Success(Some(res.copy(stmts = Seq())))
              } else {
                Success()
              }
              val newFrame = frame.copy(stmts = frame.stmts ++ res.stmts)
              newAbdRes && Q(newFrame)
          }
        }
        )
    }
  }



  /*/val tra = VarTransformer(s, v, targetVars, s.h)
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
}*/
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
