package viper.silicon.biabduction

import viper.silicon.decider.PathConditionStack
import viper.silicon.interfaces._
import viper.silicon.rules.chunkSupporter.findChunk
import viper.silicon.rules.consumer.consumes
import viper.silicon.rules.{evaluator, executionFlowController}
import viper.silicon.state._
import viper.silicon.state.terms.{Term, True}
import viper.silicon.utils.ast.BigAnd
import viper.silicon.verifier.Verifier
import viper.silver.ast._
import viper.silver.verifier.errors.Internal
import viper.silver.verifier.reasons.{InsufficientPermission, MagicWandChunkNotFound}
import viper.silver.verifier.{DummyReason, PartialVerificationError, VerificationError}

trait BiAbductionResult {
  def s: State

  def v: Verifier
}

trait BiAbductionSuccess extends BiAbductionResult

// TODO nklose BiAbductionSuccess should be able to provide arbitrary transformations of methods. Then we can just
// use this for all cases and need less dummy stuff

case class AbductionSuccess(s: State, v: Verifier, pcs: PathConditionStack, state: Seq[(Exp, Option[BasicChunk])] = Seq(), stmts: Seq[Stmt] = Seq(), newFieldChunks: Map[BasicChunk, LocationAccess], trigger: Option[Positioned] = None) extends BiAbductionSuccess {

  val preTrans = VarTransformer

  override def toString: String = {
    "Abduced pres " + state.length + ", Abduced statements " + stmts.length
  }

  def addToMethod(m: Method, bcExps: Seq[Exp], newFieldChunks: Map[BasicChunk, LocationAccess]): Option[Method] = {
    val ins = m.formalArgs.map(_.localVar)
    val preHeap = s.oldHeaps.head._2
    val preVars = s.g.values.collect { case (v, t) if ins.contains(v) => (v, t) }
    val prevPcs = v.decider.pcs
    v.decider.setPcs(pcs)
    val pres = getPreconditions(preVars, preHeap, bcExps, newFieldChunks)
    val finalStmts = getStatements(bcExps)
    v.decider.setPcs(prevPcs)
    if (pres.isEmpty || finalStmts.isEmpty) {
      None
    } else {
      val finalStmt = finalStmts.get
      val body = m.body.get
      val newBody: Seqn = trigger match {
        case None => body
        case Some(t: Stmt) if t == abductionUtils.dummyEndStmt =>
          addToInnerBody(body, finalStmt)
          //Seqn(, body.scopedSeqnDeclarations)(body.pos, body.info, body.errT)

        case Some(t: Stmt) if abductionUtils.isEndOfLoopStmt(t) =>
          val loop = abductionUtils.getWhile(t.asInstanceOf[Label].invs.head, m)
          val newLoopBody = loop.body.copy(ss = loop.body.ss ++ finalStmt)(pos = loop.body.pos, info = loop.body.info, errT = loop.body.errT)
          val newLoop = loop.copy(body = newLoopBody)(loop.pos, loop.info, loop.errT)
          body.transform { case stmt if stmt == loop => newLoop }
        case Some(t: Stmt) =>
          body.transform {
            case stmt if stmt == t =>
              Seqn(finalStmt :+ t, Seq())(t.pos, t.info, t.errT)
          }
        case Some(e: Exp) => body.transform {
          case ifStmt: If if ifStmt.cond == e => Seqn(stmts :+ ifStmt, Seq())(ifStmt.pos, ifStmt.info, ifStmt.errT)
          case whileStmt: While if whileStmt.cond == e => Seqn(stmts :+ whileStmt, Seq())(whileStmt.pos, whileStmt.info, whileStmt.errT)
        }
      }

      Some(m.copy(pres = (m.pres ++ pres.get).distinct, body = Some(newBody))(pos = m.pos, info = m.info, errT = m.errT))
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

  def getBcExps(bcsTerms: Seq[Term]): Seq[Option[Exp]] = {
    val prevPcs = v.decider.pcs

    v.decider.setPcs(pcs)

    val varTrans = VarTransformer(s, v, s.g.values, s.h)
    val bcExps = bcsTerms.map { t => varTrans.transformTerm(t) }

    // If we can express as in vars, then we want to
    val ins = s.currentMember.get.asInstanceOf[Method].formalArgs.map(_.localVar)
    val preVars = s.g.values.collect { case (v, t) if ins.contains(v) => (v, t) }
    val preTrans = VarTransformer(s, v, preVars, s.h)
    val preExps = bcExps.map {
      case Some(t) => preTrans.transformExp(t, strict = false)
      case None => None
    }

    v.decider.setPcs(prevPcs)
    preExps
  }

  def getStatements(bcExps: Seq[Exp]): Option[Seq[Stmt]] = {
    if (stmts.isEmpty) {
      Some(Seq())
      // TODO nklose we are over approximating here, this is probably wrong in general but good in practise
      //} else if (bcExps.contains(None)) {
      //  None
    } else {
      val con = BigAnd(bcExps)
      con match {
        case _: TrueLit => Some(stmts)
        case _ => Some(Seq(If(con, Seqn(stmts, Seq())(), Seqn(Seq(), Seq())())()))
      }
    }
  }

  def getPreconditions(preVars: Map[AbstractLocalVar, (Term, Option[Exp])], preHeap: Heap, bcExps: Seq[Exp], newFieldChunks: Map[BasicChunk, LocationAccess]): Option[Seq[Exp]] = {

    if (state.isEmpty) {
      Some(Seq())
    } else {

      val varTrans = VarTransformer(s, v, preVars, preHeap, newFieldChunks)
      val presTransformed = state.map { pre =>
        varTrans.transformExp(pre._1)
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

  /*
  def addToMethod(m: Method, bcs: Seq[Term]): Option[Method] = {

    val bcExps = getBcsExps(bcs)
    if (bcExps.contains(None)) {
      None
    } else {
      val con = BigAnd(bcExps.map { case Some(e) => e })
      val inv = con match {
        case _: TrueLit => BigAnd(invs)
        case _ => Implies(con, BigAnd(invs))()
      }
      val body = m.body.get
      val newBody = body.transform {
        case l: While if l.cond == loop.cond =>
          l.copy(invs = l.invs :+ inv)(pos = l.pos, info = l.info, errT = l.errT)
        case other => other
      }
      Some(m.copy(body = Some(newBody))(pos = m.pos, info = m.info, errT = m.errT))
    }
  }*/
}

case class FramingSuccess(s: State, v: Verifier, posts: Seq[Exp], loc: Positioned, pcs: PathConditionStack, varTran: VarTransformer) extends BiAbductionSuccess {
  override def toString: String = "Successful framing"

  def getBcExps(bcsTerms: Seq[Term], targetVars: Map[AbstractLocalVar, (Term, Option[Exp])]): Seq[Exp] = {
    val varTrans = VarTransformer(s, v, targetVars, s.h)
    val bcExps = bcsTerms.map { t => varTrans.transformTerm(t) }

    // TODO this is possibly unsound but better in practise
    bcExps.collect { case Some(e) => e }
    /*
    if (bcExps.contains(None)) {
      None
    } else {
      Some(BigAnd(bcExps.map { case Some(e) => e }))
    }*/
  }

  /*
    def addToMethod(m: Method, bcs: Seq[Term]): Option[Method] = {
      val prevPcs = v.decider.pcs
      v.decider.setPcs(pcs)
      val formals = m.formalArgs.map(_.localVar) ++ m.formalReturns.map(_.localVar)
      val vars = s.g.values.collect { case (var2, t) if formals.contains(var2) => (var2, t) }
      val bcExps = getBcExps(bcs, vars)
      v.decider.setPcs(prevPcs)

      /*
      val bcStmts = (bcExps, stmts) match {
        case (_, Seq()) => Seq()
        case (_: TrueLit, _) => stmts
        case _ => Seq(If(bcExps, Seqn(stmts, Seq())(), Seqn(Seq(), Seq())())())
      }*/

      val bcPost = (bcExps, posts) match {
        case (_, Seq()) => Seq()
        case (Seq(), _) => posts
        case _ => Seq(Implies(BigAnd(bcExps), BigAnd(posts))())
      }

      //val body = m.body.get
      //val newBody = body.copy(ss = body.ss ++ bcStmts)(pos = body.pos, info = body.info, errT = body.errT)
      Some(m.copy(posts = m.posts ++ bcPost)(pos = m.pos, info = m.info, errT = m.errT))

    }*/
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

  def solveAbductionForError(s: State, v: Verifier, f: Failure, stateAllowed: Boolean, trigger: Option[Positioned] = None)(Q: (State, Verifier) => VerificationResult): VerificationResult = {

    if (!s.doAbduction) {
      f
    } else {

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

          val qPre = AbductionQuestion(s, v, Seq(abdGoal), stateAllowed = stateAllowed, trigger = trigger)
          val q = tra match {
            case Some(trafo) => trafo.f(qPre).asInstanceOf[AbductionQuestion]
            case _ => qPre
          }
          AbductionApplier.applyRules(q) {
            q1 =>
              if (q1.goal.isEmpty) {
                val newState = q1.foundState.reverse
                val newStmts = q1.foundStmts

                // TODO nklose created chunks can go away again before we finish abduction, due to a package or a fold
                // We have to do this in place when the chunks are created and not here
                //abductionUtils.findChunks(newLocs, q1.s, q1.v, Internal()) { newChunks =>
                if (q1.v.decider.checkSmoke()) {
                  Success(Some(BiAbductionFailure(s, v, initPcs)))
                } else {
                  val newChunks = newState.collect { case (e, c: Some[BasicChunk]) => c.get }
                  val newOldHeaps = q1.s.oldHeaps.map { case (label, heap) => (label, heap + Heap(newChunks)) }
                  val s1 = q1.s.copy(oldHeaps = newOldHeaps)
                  val fieldChunks = newState.collect { case (fa: FieldAccessPredicate, c) => (c.get, fa.loc) }.toMap
                  val abd = AbductionSuccess(s1, q1.v, q1.v.decider.pcs.duplicate(), newState, newStmts, fieldChunks, trigger)
                  Success(Some(abd)) && Q(s1, q1.v)
                }
                //}
              } else {
                f
              }
          }
      }
    }
  }

  def solveAbstraction(s: State, v: Verifier)(Q: (State, Seq[Exp], Verifier) => VerificationResult): VerificationResult = {
    val q = AbstractionQuestion(s, v)
    AbstractionApplier.applyRules(q) { q1 =>
      val res = VarTransformer(q1.s, q1.v, q1.s.g.values, q1.s.h).transformState(q1.s)
      Q(q1.s, res, q1.v)
    }
  }

  def solveFraming(s: State, v: Verifier, pvef: Exp => PartialVerificationError, tra: VarTransformer, loc: Positioned, knownPosts: Seq[Exp], stateAllowed: Boolean)(Q: FramingSuccess => VerificationResult): VerificationResult = {

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
        BiAbductionSolver.solveAbductionForError(s, v, f, stateAllowed, Some(loc))((s3, v3) => {
          solveFraming(s3, v3, pvef, tra, loc, knownPosts, stateAllowed)(Q)

          /*{
            frame =>
              val newAbdRes = if (res.state.nonEmpty) {
                Success(Some(res.copy(stmts = Seq())))
              } else {
                Success()
              }
              //val newFrame = frame.copy(stmts = frame.stmts ++ res.stmts)
              Q(frame)
          }*/
        }
        )
    }
  }

  def resolveAbductionResults(m: Method, nf: NonFatalResult): Option[Method] = {
    val abdReses = abductionUtils.getAbductionSuccesses(nf)
    val newMatches = abdReses.flatMap(_.newFieldChunks).toMap
    val abdCases = abdReses.groupBy(res => (res.trigger, res.stmts, res.state))

    // Try to join by bc terms
    val joinedCases = abdCases.flatMap {
      case (_, reses) =>
        val unjoined = reses.map(res =>

          (Seq(res), res.pcs.branchConditions.distinct.filter(_ != True)))
        val termJoined = abductionUtils.joinBcs(unjoined)

        // Now transform to exp, remove Nones and join again. TODO: Removing Nones here might be unsound
        // That is why we do as much as possible on term level to avoid this as much as possible
        val expUnjoined = termJoined.map {
          case (reses, bcTerms) =>
            reses -> reses.head.getBcExps(bcTerms).distinct.collect { case Some(bc) => bc }
        }
        expUnjoined.groupBy(_._2).map { case (bcs, list) => list.head._1.head -> bcs }
    }

    // We want to add things in the reverse order of the abduction results.
    abdReses.reverse.foldLeft[Option[Method]](Some(m)) { (mOpt, res) =>
      mOpt match {
        case Some(m1) if joinedCases.contains(res) => res.addToMethod(m1, joinedCases(res), newMatches)
        case _ => mOpt
      }
    }
    //joinedCases.foldLeft[Option[Method]](Some(m))((m1, res) => m1.flatMap { mm => res._1.addToMethod(mm, res._2, newMatches) })
  }


  def resolveFramingResults(m: Method, nf: NonFatalResult): Option[Method] = {
    val frames = abductionUtils.getFramingSuccesses(nf)

    // We get a framing result for every branch.
    // So postconditions that are in every branch can just be added without any bcs
    val everyPosts = frames.head.posts.filter { p => frames.forall(_.posts.contains(p)) }

    val formals = m.formalArgs.map(_.localVar) ++ m.formalReturns.map(_.localVar)
    val vars = frames.head.s.g.values.collect { case (var2, t) if formals.contains(var2) => (var2, t) }


    val cases = frames.map(f => (f.posts.diff(everyPosts), f.getBcExps(f.pcs.branchConditions.distinct.filter(_ != True), vars))).distinct

    // We can remove bcs that hold in every branch
    val everyTerms = cases.head._2.filter { t => cases.forall(_._2.contains(t)) }

    val res = cases.collect {
      case (posts, bcs) if posts.nonEmpty && bcs.diff(everyTerms).nonEmpty => Implies(BigAnd(bcs.diff(everyTerms)), BigAnd(posts))()
      case (posts, _) if posts.nonEmpty => BigAnd(posts)
    } ++ everyPosts
    Some(m.copy(posts = m.posts ++ res)(pos = m.pos, info = m.info, errT = m.errT))

    /*
    val frameCases = frames.groupBy(f => f.posts.diff(everyPosts)).flatMap {
      case (_, frs) =>
        val unjoined = frs.map(fr => (Seq(fr), fr.pcs.branchConditions.distinct.filter(_ != True)))
        val joined = abductionUtils.joinBcs(unjoined)
        joined.map {
          case (frs, pcs) =>
            frs.head -> pcs
        }
    }

    frameCases.foldLeft[Option[Method]](Some(m))((m1, res) => m1.flatMap { mm => res._1.addToMethod(mm, res._2.diff(alwaysTerms)) })
  */

  }


  def resolveLoopInvResults(m: Method, nf: NonFatalResult): Option[Method] = {

    val invsSuccs = abductionUtils.getInvariantSuccesses(nf)

    val reses = invsSuccs.groupBy(inv => inv.loop).map {
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

    Some(reses.foldLeft(m) { case (m1, (loop, inv)) =>
      val body = m1.body.get
      val newBody = body.transform {
        case l: While if l.cond == loop.cond =>
          l.copy(invs = l.invs ++ inv)(pos = l.pos, info = l.info, errT = l.errT)
        case other => other
      }
      m1.copy(body = Some(newBody))(pos = m.pos, info = m.info, errT = m.errT)
    })

    /*
    val invCases = invs.groupBy(inv => (inv.loop, inv.invs)).flatMap {
      case (_, invs) =>
        val unjoined = invs.map(inv => (Seq(inv), inv.pcs.branchConditions.distinct.filter(_ != True)))
        val joined = abductionUtils.joinBcs(unjoined)
        joined.map {
          case (invs, pcs) =>
            invs.head -> pcs
        }
    }
    invCases.foldLeft[Option[Method]](Some(m))((m1, res) => m1.flatMap { mm => res._1.addToMethod(mm, res._2) })*/
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
      case w: While if w.cond == condition => w
    }.get
  }

  def joinBcs[T](bcs: Seq[(Seq[T], Seq[Term])]): Seq[(Seq[T], Seq[Term])] = {
    bcs.combinations(2).collectFirst {
      case Seq((a_res, a_pcs), (b_res, b_pcs)) if canJoin(a_pcs, b_pcs).isDefined =>
        val rest = bcs.filter { case (c_res, _) => c_res != a_res && c_res != b_res }
        val joined = canJoin(a_pcs, b_pcs).get
        joinBcs(rest :+ (a_res ++ b_res, joined))
    } match {
      case Some(joined) => joined
      case None => bcs
    }
  }

  private def canJoin(a: Seq[Term], b: Seq[Term]): Option[Seq[Term]] = {
    (a.diff(b), b.diff(a)) match {
      case (Seq(eq: terms.BuiltinEquals), Seq(terms.Not(t))) if eq == t => Some(a.filter(_ != eq))
      case (Seq(terms.Not(t)), Seq(eq: terms.BuiltinEquals)) if eq == t => Some(b.filter(_ != eq))
      case (Seq(), _) => Some(a)
      case (_, Seq()) => Some(b)
      case _ => None
    }
  }

  private def findChunkFromExp(loc: LocationAccess, s: State, v: Verifier, pve: PartialVerificationError)(Q: Option[BasicChunk] => VerificationResult): VerificationResult = {

    val arg = loc match {
      case FieldAccess(rcv, _) => rcv
      case PredicateAccess(args, _) => args.head
    }
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

  // We need to sort exps before producing them because we have to create fields before creating stuff on the fields
  // The idea is that the length of something on the field will always be greater than the field itself.
  def sortExps(exps: Seq[Exp]): Seq[Exp] = {
    exps.sortBy(e => e.size)
  }

}
