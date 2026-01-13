package viper.silicon.biabduction

import viper.silicon.decider.PathConditionStack
import viper.silicon.interfaces._
import viper.silicon.rules.consumer.consumes
import viper.silicon.rules.executionFlowController
import viper.silicon.state._
import viper.silicon.state.terms.{Term, True}
import viper.silicon.utils.ast.{BigAnd, BigOr}
import viper.silicon.verifier.Verifier
import viper.silver.ast._
import viper.silver.parser.PKw.{Ensures, Invariant, Requires}
import viper.silver.verifier.errors.Internal
import viper.silver.verifier.reasons.{InsufficientPermission, MagicWandChunkNotFound}
import viper.silver.verifier.{DummyReason, PartialVerificationError, VerificationError}

import scala.annotation.tailrec

case class InferenceResult(start: HasLineColumn, end: HasLineColumn, newText: String)

trait BiAbductionResult {
  def s: State

  def v: Verifier
}

trait BiAbductionSuccess extends BiAbductionResult

case class AbductionSuccess(s: State, v: Verifier, pcs: PathConditionStack, state: Seq[(Exp, Option[BasicChunk])] = Seq(), stmts: Seq[Stmt] = Seq(), newFieldChunks: Map[BasicChunk, LocationAccess], allNewChunks: Seq[BasicChunk], trigger: Option[Positioned] = None) extends BiAbductionSuccess {

  override def toString: String = {
    "Abduced pres " + state.length + ", Abduced statements " + stmts.length
  }

  def getBcExps(bcsTerms: Seq[Term]): Seq[Option[Exp]] = {
    val prevPcs = v.decider.pcs

    v.decider.setPcs(pcs)

    // If we can express as in vars, then we want to
    val ins = s.currentMember.get.asInstanceOf[Method].formalArgs.map(_.localVar)
    val preVars = s.g.values.collect { case (v, t) if ins.contains(v) => (v, t) }

    val otherVars: Map[AbstractLocalVar, (Term, Option[Exp])] = s.g.values
    val varTrans = VarTransformer(s, v, preVars, s.h, otherVars = otherVars)
    val bcExps = bcsTerms.map { t => varTrans.transformTerm(t) }
    
    v.decider.setPcs(prevPcs)
    bcExps
  }

  def getStatements(bcExps: Seq[Exp]): Option[Seq[Stmt]] = {
    if (stmts.isEmpty) {
      Some(Seq())
      // We are over-approximating here, this is wrong in general but good in practise
      //} else if (bcExps.contains(None)) {
      //  None
    } else {
      val con = BigAnd(bcExps)
      con match {
        case _: TrueLit => Some(stmts.reverse)
        case _ => Some(Seq(If(con, Seqn(stmts.reverse, Seq())(), Seqn(Seq(), Seq())())()))
      }
    }
  }

  def getPreconditions(preVars: Map[AbstractLocalVar, (Term, Option[Exp])], preHeap: Heap, bcExps: Seq[Exp], newFieldChunks: Map[BasicChunk, LocationAccess]): Option[Seq[Exp]] = {

    if (state.isEmpty) {
      Some(Seq())
    } else {

      val varTrans = VarTransformer(s, v, preVars, preHeap, newFieldChunks)
      val presTransformed = state.collect {
        case (pre, Some(ch)) => varTrans.transformChunk(ch)
        //case (pre, None) => varTrans.transformExp(pre)
      }
      val bcPreExps = bcExps.collect {
        case exp => varTrans.transformExp(exp)
      }

      // If we cannot express the precondition, we have to fail
      // If we fail to express some branch conditions, we can overapproximate the precondition
      if (presTransformed.contains(None)) {
        None
      } else {
        val pres = presTransformed.collect { case Some(e) => e }
        val bcs = BigAnd(bcPreExps.collect { case Some(e) => e })
        bcs match {
          case _: TrueLit => Some(pres)
          case _ => Some(Seq(Implies(bcs, BigAnd(pres))()))
        }
      }
    }
  }
}

case class LoopInvariantSuccess(s: State, v: Verifier, invs: Seq[Exp] = Seq(), loop: While, pcs: PathConditionStack) extends BiAbductionSuccess {
  override def toString: String = "Successful loop invariant abduction"

  def getBcsExps(bcs: Seq[Term]): Seq[Exp] = {
    val prevPcs = v.decider.pcs
    v.decider.setPcs(pcs)
    val bcTran = VarTransformer(s, v, s.g.values, s.h)
    val bcExps = bcs.map { t => bcTran.transformTerm(t) }.collect { case Some(e) => e }
    v.decider.setPcs(prevPcs)
    bcExps
  }
}

case class FramingSuccess(s: State, v: Verifier, posts: Seq[Exp], loc: Positioned, pcs: PathConditionStack, varTran: VarTransformer) extends BiAbductionSuccess {
  override def toString: String = "Successful framing"

  def getBcExps(bcsTerms: Seq[Term], prefVars: Map[AbstractLocalVar, (Term, Option[Exp])], otherVars: Map[AbstractLocalVar, (Term, Option[Exp])]): Seq[Exp] = {
    val varTrans = VarTransformer(s, v, prefVars, s.h, otherVars = otherVars)
    val bcExps = bcsTerms.map { t => varTrans.transformTerm(t) }
    bcExps.collect { case Some(e) => e.topLevelConjuncts }.flatten.distinct
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

  def solveAbductionForFailure(s: State, v: Verifier, f: Failure, stateAllowed: Boolean, trigger: Option[Positioned] = None)(Q: (State, Verifier) => VerificationResult): VerificationResult = {
    if (!s.doAbduction) {
      f
    } else {
      solveAbductionForError(s, v, f.message, stateAllowed, trigger) {
        case None => f
        case fail@Some(_: BiAbductionFailure) =>
          Success(fail)
        case suc@Some(abd: AbductionSuccess) =>
          Success(suc) && Q(abd.s, abd.v)
      }
    }
  }

  def solveAbductionForError(s: State, v: Verifier, err: VerificationError, stateAllowed: Boolean, trigger: Option[Positioned] = None)(Q: Option[BiAbductionResult] => VerificationResult): VerificationResult = {

    val initPcs = v.decider.pcs.duplicate()

    val reason = err.reason match {
      case reason: InsufficientPermission =>
        val acc = reason.offendingNode match {
          case n: FieldAccess => FieldAccessPredicate(n, Some(FullPerm()()))()
          case n: PredicateAccess => PredicateAccessPredicate(n, Some(FullPerm()()))()
        }
        Some(acc)
      case reason: MagicWandChunkNotFound => Some(reason.offendingNode)
      case _ => None
    }

    reason match {
      case None => Q(None)
      case Some(abdGoal) =>

        val tra = err.failureContexts.collectFirst {
          case SiliconAbductionFailureContext(trafo, None) if trafo.isDefined => trafo.get
        }

        val qPre = AbductionQuestion(s, v, Seq(abdGoal), stateAllowed = stateAllowed, trigger = trigger)
        val q = tra match {
          case Some(trafo) => trafo.f(qPre).asInstanceOf[AbductionQuestion]
          case _ => qPre
        }
        // We skip the first rule because we know that an error occurred, so we cannot be done
        // This allows us to fold on null references multiple times, as is required for e.g. trees.
        AbductionApplier.applyRules(q, currentRule = 1) {
          q1 =>
            if (q1.goal.isEmpty) {
              val newState = q1.foundState.reverse
              val newStmts = q1.foundStmts

              if (q1.v.decider.checkSmoke()) {
                Q(Some(BiAbductionFailure(s, v, initPcs)))
              } else {
                val newChunks = newState.collect { case (_, c: Some[BasicChunk]) => c.get }
                val fieldChunks = newState.collect { case (fa: FieldAccessPredicate, c) => (c.get, fa.loc) }.toMap
                val abd = AbductionSuccess(q1.s, q1.v, q1.v.decider.pcs.duplicate(), newState, newStmts, fieldChunks, newChunks, trigger)
                Q(Some(abd))
              }
            } else {
              Q(None)
            }
        }
    }
  }

  def solveAbstraction(s: State, v: Verifier)(Q: (State, Seq[Exp], Verifier) => VerificationResult): VerificationResult = {
    val q = AbstractionQuestion(s, v)
    AbstractionApplier.applyRules(q) { q1 =>
      val absTransForm = VarTransformer(q1.s, q1.v, q1.s.g.values, q1.s.h)
      val res = absTransForm.transformState(q1.s)
      Q(q1.s, res, q1.v)
    }
  }

  def solveFraming(s: State, v: Verifier, pvef: Exp => PartialVerificationError, tra: VarTransformer, loc: Positioned, knownPosts: Seq[Exp], stateAllowed: Boolean)(Q: FramingSuccess => VerificationResult): VerificationResult = {

    //val tra = VarTransformer(s, v, targetVars, s.h)
    executionFlowController.tryOrElse1[Option[Term]](s, v) { (s, v, QS) =>
      consumes(s, knownPosts, returnSnap = false, pvef, v)(QS)
    } { (s1: State, _: Option[Term], v1: Verifier) =>
      executionFlowController.locallyWithResult[Seq[Exp]](s1, v1) { (s1a, v1a, T) =>
        BiAbductionSolver.solveAbstraction(s1a, v1a) { (s2, framedPosts, v2) =>
          val newPosts = framedPosts.map { e => tra.transformExp(e) }.collect { case Some(e) => e }
          T(newPosts)
        }
      } {
        // We consumed all the posts and did not find any new ones. So create a fresh Framing Success with the bcs
        case Seq() =>
          Q(FramingSuccess(s1, v1, Seq(), loc, v.decider.pcs.duplicate(), tra)) // No new state or needed stmts
        // We consumed the post conditions and found new ones. Handle the new ones and add them to the result
        case newPosts1 =>
          solveFraming(s1, v1, pvef, tra, loc, newPosts1, stateAllowed) { frame =>
            val newFrame = frame.copy(posts = frame.posts ++ newPosts1)
            Q(newFrame)
          }
      }
    } {
      // We failed to fulfill the posts. Perform abduction, add the results and try again.
      f =>
        BiAbductionSolver.solveAbductionForFailure(s, v, f, stateAllowed, Some(loc))((s3, v3) => {
          solveFraming(s3, v3, pvef, tra, loc, knownPosts, stateAllowed)(Q)
        }
        )
    }
  }

  def resolveAbductionResults(m: Method, nf: NonFatalResult): Option[(Method, Seq[InferenceResult])] = {
    val abdReses = abductionUtils.getAbductionSuccesses(nf)
    val newMatches = abdReses.flatMap(_.newFieldChunks).toMap
    val abdCases = abdReses.groupBy(res => (res.trigger.get, res.trigger.get.pos, res.stmts, res.state))

    // Try to join by bc terms
    val joinedCases = abdCases.map {
      case (_, reses) =>
        val unjoined = reses.map(res =>

          (Seq(res), res.pcs.branchConditions.flatMap{
            case terms.And(terms) => terms
            case term => Seq(term)
          }.distinct.filter(_ != True)))
        val termJoined = abductionUtils.joinBcsTerms(unjoined)

        // Now transform to exp, remove Nones and join again. TODO: Removing Nones here might be unsound
        // That is why we do as much as possible on term level to avoid this as much as possible
        val expUnjoined = termJoined.map {
          case (reses, bcTerms) =>
            reses -> reses.head.getBcExps(bcTerms).collect { case Some(bc) => bc }.flatMap(_.topLevelConjuncts).distinct
        }
        val expJoined = abductionUtils.joinBcsExps(expUnjoined)

        val abdRes = expJoined.head._1.head
        val finalBcs = BigOr(expJoined.map(e => BigAnd(e._2)))
        abdRes -> finalBcs
    }

    // We want to add things in the reverse order of the abduction results.
    abdReses.reverse.foldLeft[Option[(Method, Seq[InferenceResult])]](Some((m, Seq.empty))) {
      case (Some((m1, infs)), res) =>
        joinedCases.get(res) match {
          case Some(joinedCase) =>
            addToMethod(m1, Seq(joinedCase), newMatches, res).map { case (m2, newInfs) =>
              (m2, infs ++ newInfs)
            }
          case None => Some((m1, infs))
        }
      case (None, _) => None
    }
  }

  private def addToMethod(m: Method, bcExps: Seq[Exp], newFieldChunks: Map[BasicChunk, LocationAccess], abdRes: AbductionSuccess): Option[(Method, Seq[InferenceResult])] = {

    val s = abdRes.s
    val v = abdRes.v

    val ins = m.formalArgs.map(_.localVar)
    val preHeap = s.oldHeaps.head._2
    val preVars = s.g.values.collect { case (v, t) if ins.contains(v) => (v, t) }
    val prevPcs = v.decider.pcs
    v.decider.setPcs(abdRes.pcs)
    val pres = abdRes.getPreconditions(preVars, preHeap, bcExps, newFieldChunks)
    val finalStmts = abdRes.getStatements(bcExps)
    v.decider.setPcs(prevPcs)
    if (pres.isEmpty || finalStmts.isEmpty) {
      None
    } else {
      val finalStmt = finalStmts.get
      val body = m.body.get
      val (newBody: Seqn, stmtInfRes: Seq[InferenceResult]) = abdRes.trigger match {
        case _ if finalStmt.isEmpty => (body, Seq())
        case None => (body, Seq())
        case Some(t: Stmt) if t == abductionUtils.dummyEndStmt =>
          val newBody = addToInnerBody(body, finalStmt)
          val infPos = LineColumnPosition(m.pos.asInstanceOf[SourcePosition].end.get.line, m.pos.asInstanceOf[SourcePosition].end.get.column)
          val infRes = finalStmt.map(stmt => InferenceResult(infPos, infPos, stmt.toString() + "\n"))
          (newBody, infRes)

        case Some(t: Stmt) if abductionUtils.isEndOfLoopStmt(t) =>
          val loop = abductionUtils.getWhile(t.asInstanceOf[Label].invs.head, m)
          val newLoopBody = loop.body.copy(ss = loop.body.ss ++ finalStmt)(pos = loop.body.pos, info = loop.body.info, errT = loop.body.errT)
          val newLoop = loop.copy(body = newLoopBody)(loop.pos, loop.info, loop.errT)
          val newBody = body.transform { case stmt if stmt == loop => newLoop }

          val infPos = LineColumnPosition(loop.pos.asInstanceOf[SourcePosition].end.get.line, loop.pos.asInstanceOf[SourcePosition].end.get.column)
          val infRes = finalStmt.map(stmt => InferenceResult(infPos, infPos, stmt.toString() + "\n"))
          (newBody, infRes)

        case Some(t: Stmt) =>
          val newBody = body.transform {
            case stmt: Stmt if stmt == t && stmt.pos == t.pos =>
              Seqn(finalStmt :+ t, Seq())(t.pos, t.info, t.errT)
          }
          val infPos = LineColumnPosition(t.pos.asInstanceOf[SourcePosition].start.line, t.pos.asInstanceOf[SourcePosition].start.column)
          val infRes = finalStmt.map(stmt => InferenceResult(infPos, infPos, stmt.toString() + "\n"))
          (newBody, infRes)

        case Some(e: Exp) =>

          val t = body.collectFirst {
            case ifStmt: If if ifStmt.cond == e && ifStmt.cond.pos == e.pos => ifStmt
            case whileStmt: While if whileStmt.cond == e && whileStmt.cond.pos == e.pos => whileStmt
          }.get
          val newBody = body.transform {
            case t1: Stmt if t==t1 => Seqn(abdRes.stmts :+ t1, Seq())(t1.pos, t1.info, t1.errT)
          }
          val infPos = LineColumnPosition(t.pos.asInstanceOf[SourcePosition].start.line, t.pos.asInstanceOf[SourcePosition].start.column)
          val infRes = abdRes.stmts.map(stmt => InferenceResult(infPos, infPos, stmt.toString() + "\n"))
          (newBody, infRes)
      }

      val finalM = m.copy(pres = abductionUtils.sortExps(pres.get ++ m.pres).distinct, body = Some(newBody))(pos = m.pos, info = m.info, errT = m.errT)

      val prePos = m.posts match {
        case Seq() => getInnerLocation(body).start.line
        case posts => posts.head.pos.asInstanceOf[SourcePosition].start.line
      }
      val preInfs = pres.get.reverse.map { pre =>
        val insert = LineColumnPosition(prePos, m.pos.asInstanceOf[SourcePosition].start.column)
        InferenceResult(insert, insert, Requires.keyword + " " + pre.toString + "\n")
      }

      Some((finalM, preInfs ++ stmtInfRes))
    }
  }

  private def addToInnerBody(outer: Seqn, bcStmts: Seq[Stmt]): Seqn = {
    outer match {
      case o@Seqn(Seq(in: Seqn), _) =>
        val newInner = addToInnerBody(in, bcStmts)
        o.copy(ss = Seq(newInner))(o.pos, o.info, o.errT)
      case in => in.copy(ss = in.ss ++ bcStmts)(pos = in.pos, info = in.info, errT = in.errT)
    }
  }

  @tailrec
  private def getInnerLocation(outer: Seqn): SourcePosition = {
    outer match {
      case o@Seqn(Seq(in: Seqn), _) if !o.pos.isInstanceOf[SourcePosition] =>
        getInnerLocation(in)
      case in => in.pos.asInstanceOf[SourcePosition]
    }
  }


  def resolveFramingResults(m: Method, nf: NonFatalResult): Seq[Exp] = {
    abductionUtils.getFramingSuccesses(nf) match {
      case Seq() => Seq()
      case frames =>

      // We get a framing result for every branch.
      // So postconditions that are in every branch can just be added without any bcs
      val everyPosts = frames.head.posts.filter { p => frames.forall(_.posts.contains(p)) }

      val cases = frames.map { f =>
        val prefVars = f.s.g.values.collect { case (var2, t) if m.formalArgs.map(_.localVar).contains(var2) => (var2, t) }
        val otherVars = f.s.g.values.collect { case (var2, t) if m.formalReturns.map(_.localVar).contains(var2) => (var2, t) }
        val bcs = f.pcs.branchConditions.flatMap {
          case terms.And(terms) => terms
          case term => Seq(term)
        }.distinct.filter(_ != True)
        (f.posts.diff(everyPosts), f.getBcExps(bcs, prefVars, otherVars))
      }.distinct

      // We can remove bcs that hold in every branch
      val everyTerms = cases.head._2.filter { t => cases.forall(_._2.contains(t)) }

      cases.collect {
        case (posts, bcs) if posts.nonEmpty && bcs.diff(everyTerms).nonEmpty => Implies(BigAnd(bcs.diff(everyTerms)), BigAnd(posts))()
        case (posts, _) if posts.nonEmpty => BigAnd(posts)
      } ++ everyPosts
    }
  }

  def addPostResults(m: Method, reses: Seq[Exp]): Method = {
    m.copy(posts = m.posts ++ reses)(pos = m.pos, info = m.info, errT = m.errT)
  }

  def generatePostFixes(m: Method, reses: Seq[Exp]): Seq[InferenceResult] = {

    val column = m.pos.asInstanceOf[SourcePosition].start.column
    val line = m.posts match {
      case Seq() => getInnerLocation(m.body.get).start.line
      case posts => posts.head.pos.asInstanceOf[SourcePosition].start.line
    }

    reses.reverse.map{ res =>
      val insert = LineColumnPosition(line, column)
      InferenceResult(insert, insert, Ensures.keyword + " " + res.toString + "\n")
    }
  }


  def resolveLoopInvResults(nf: NonFatalResult): Map[While, Seq[Exp]] = {

    val invsSuccs = abductionUtils.getInvariantSuccesses(nf)

    // there is an issue here if the same loop is repeated twice in the same method
    invsSuccs.groupBy(inv => inv.loop).map {
      case (loop, cases) =>

        // We get an invariant for each time we reach a loop. So if an invariant holds every time we get there
        // we can ignore the bcs
        val everyInv = cases.head.invs.filter { i => cases.forall(_.invs.contains(i)) }
        val everyBcs = cases.head.pcs.branchConditions.filter { t => cases.forall(_.pcs.branchConditions.contains(t)) } :+ True

        val invsWithBcs = cases.map { inv =>
          val bcs = inv.getBcsExps(inv.pcs.branchConditions.distinct.filter(!everyBcs.contains(_)))
          (inv.invs.diff(everyInv), bcs.diff(everyBcs))
        }

        val res = invsWithBcs.collect {
          case (is, bcs) if is.nonEmpty && bcs.nonEmpty => Implies(BigAnd(bcs.diff(everyBcs)), BigAnd(is))()
          case (is, _) if is.nonEmpty => BigAnd(is)
        } ++ everyInv

        (loop, res)
    }
  }

  def addLoopInvResults(m: Method, reses: Map[While, Seq[Exp]]): Method = {
    reses.foldLeft(m) { case (m1, (loop, inv)) =>
      val body = m1.body.get
      val newBody = body.transform {
        case l: While if l.cond == loop.cond && l.cond.pos == loop.cond.pos =>
          val newInvs = abductionUtils.sortExps(inv ++ l.invs)
          l.copy(invs = newInvs)(pos = l.pos, info = l.info, errT = l.errT)
        case other => other
      }
      m1.copy(body = Some(newBody))(pos = m.pos, info = m.info, errT = m.errT)
    }
  }

  def generateLoopInvFixes(reses: Map[While, Seq[Exp]]): Seq[InferenceResult] = {

    reses.flatMap{ case (loop, invs) =>
      val column = loop.pos.asInstanceOf[SourcePosition].start.column
      val insert = loop.invs match {
        // If there are no invariants yet, we add them above the body
        case Seq() => LineColumnPosition(loop.body.pos.asInstanceOf[SourcePosition].start.line, column)
        case existingInvs => LineColumnPosition(existingInvs.head.pos.asInstanceOf[SourcePosition].start.line, column)
      }
      invs.reverse.map(inv => InferenceResult(insert, insert, Invariant.keyword + " " + inv.toString + "\n"))
    }.toSeq
  }
}


