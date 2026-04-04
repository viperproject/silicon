package viper.silicon.biabduction

import viper.silicon
import viper.silicon.biabduction.abductionUtils.pve
import viper.silicon.decider.PathConditionStack
import viper.silicon.interfaces._
import viper.silicon.interfaces.state.Chunk
import viper.silicon.rules.chunkSupporter.findChunk
import viper.silicon.rules.consumer.consumes
import viper.silicon.rules.evaluator.eval
import viper.silicon.rules.{evaluator, executionFlowController, executor, producer}
import viper.silicon.state._
import viper.silicon.state.terms.{Term, True}
import viper.silicon.utils.ast.{BigAnd, BigOr}
import viper.silicon.utils.freshSnap
import viper.silicon.verifier.Verifier
import viper.silver.ast._
import viper.silver.utility.Common.Rational
import viper.silver.verifier.errors.Internal
import viper.silver.verifier.reasons.{AssertionFalse, InsufficientPermission, MagicWandChunkNotFound}
import viper.silver.verifier.{DummyReason, PartialVerificationError, VerificationError}

import scala.annotation.tailrec

trait BiAbductionResult {
  def s: State

  def v: Verifier
}

trait BiAbductionSuccess extends BiAbductionResult

// TODO nklose BiAbductionSuccess should be able to provide arbitrary transformations of methods. Then we can just
// use this for all cases and need less dummy stuff

case class AbductionSuccess(s: State, v: Verifier, pcs: PathConditionStack, state: Seq[(Exp, Option[BasicChunk])] = Seq(), stmts: Seq[Stmt] = Seq(), newFieldChunks: Map[BasicChunk, LocationAccess], allNewChunks: Seq[BasicChunk], trigger: Option[Positioned] = None) extends BiAbductionSuccess {

  override def toString: String = {
    s"Abduced ${state.length} pres: $state triggered by ${trigger.getOrElse("{}")}, Abduced ${stmts.length} statements $stmts"
  }

  def getBcExps(bcsTerms: Seq[Term]): Seq[Option[Exp]] = {
    val prevPcs = v.decider.pcs

    v.decider.setPcs(pcs)

    //val varTran = VarTransformer(s, v, s.g.values, s.h)
    //val preExps = bcExps.map {
    //  case Some(t) => preTrans.transformExp(t, strict = false)
    //  case None => None
    //}


    // If we can express as in vars, then we want to
    val ins = s.currentMember.get.asInstanceOf[Method].formalArgs.map(_.localVar)
    val preVars = s.g.values.collect { case (v, t) if ins.contains(v) => (v, t) }

    val otherVars: Map[AbstractLocalVar, (Term, Option[Exp])] = s.g.values
    val varTran = VarTransformer(s, v, preVars, s.h, otherVars = otherVars)
    val bcExps = bcsTerms.map { t =>
      val t1 = varTran.transformTerm(t)
      t1
    }

    v.decider.setPcs(prevPcs)
    bcExps
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
        case _: TrueLit => Some(stmts.reverse)
        case _ => Some(Seq(If(con, Seqn(stmts.reverse, Seq())(), Seqn(Seq(), Seq())())()))
      }
    }
  }

  def getPreconditions(preVars: Map[AbstractLocalVar, (Term, Option[Exp])],
                       preHeap: Heap, bcExps: Seq[Exp], newFieldChunks: Map[BasicChunk, LocationAccess]): Option[Seq[Exp]] = {

    if (state.isEmpty) {
      Some(Seq())
    } else {

      val varTran = VarTransformer(s, v, preVars, preHeap, newFieldChunks)
      val presTransformed = state.collect {
        // TODO: Some(ch) has the wrong permission amount, pre, is an expression that has the right perm amount
        // probably
        case (pre, Some(ch)) => //varTran.transformChunk(ch)
          pre match {
            case ap: AccessPredicate =>
              varTran.transformChunk(ch.copy(perm = varTran.permExpToTerm(ap.perm)))
          }
      }
      val bcPreExps = bcExps.collect {
        case exp => varTran.transformExp(exp)
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
  override def toString: String = {
    s"Succesfull framing with posts $posts"
  }
  def getBcExps(bcsTerms: Seq[Term], prefVars: Map[AbstractLocalVar, (Term, Option[Exp])], otherVars: Map[AbstractLocalVar, (Term, Option[Exp])]): Seq[Exp] = {
    val varTran = VarTransformer(s, v, prefVars, s.h, otherVars = otherVars)
    val bcExps = bcsTerms.map { t => varTran.transformTerm(t) }
    bcExps.collect { case Some(e) => e.topLevelConjuncts }.flatten.distinct
  }
}

case class BiAbductionFailure(s: State, v: Verifier, pcs: PathConditionStack) extends BiAbductionResult {
  override def toString: String = "Abduction failed"

  def
  addToMethod(m: Method): Method = {
    val ins = m.formalArgs.map(_.localVar)
    val preHeap = s.oldHeaps.head._2
    val inVars = s.g.values.collect { case (v, t) if ins.contains(v) => (v, t) }
    val prevPcs = v.decider.pcs
    v.decider.setPcs(pcs)
    val varTran = VarTransformer(s, v, inVars, preHeap)
    val bcTerms = v.decider.pcs.branchConditions
    val bcExpOpt = bcTerms.map {
      bc => varTran.transformTerm(bc)
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
      val reason = f.message.reason match {
        case reason: InsufficientPermission =>
          val perm = f.message.offendingNode match {
            case _: Fold => Some(PermMul(s.abdPermScalingFactorExp, reason.permExp.getOrElse(FullPerm()()))())
            case _ => reason.permExp
          }
          val acc = reason.offendingNode match {
            case n: FieldAccess =>
              FieldAccessPredicate(n, perm)()
            case n: PredicateAccess =>
              PredicateAccessPredicate(n, perm)()
          }
          Some(acc)
        case reason: MagicWandChunkNotFound =>
          Some(reason.offendingNode)
        case AssertionFalse(assert) =>
          // println(s"Failed due to assertion in \n\t${s.h.values.mkString("\n\t")}\n\t${s.g.values.mkString("\n\t")}\nwith pcs ${v.decider.pcs}")
          f.message.offendingNode match {
            case _: Fold => Some(Assert(assert)())
            case _ => None
          }
        case _ =>
          None
      }
      reason match {
        case None => f
        case Some(Assert(assertion)) =>
          println(s"abdGoal $assertion triggered by $trigger in s: \n\t${s.h.values.mkString("\n\t")}")
          println(s"\tdue to $f")
          // If we failed to fold a predicate because of an assertion, we try producing the assertion in the state and continuing
          executionFlowController.tryOrElse0(s, v) { (s1, v1, T) =>
            producer.produce(s1, freshSnap, assertion, pve, v1) { (s2, v2) =>
              T(s2, v2)
            }
          } {
            (s1a, v1a) =>
              val abd = AbductionSuccess(s1a, v1a, v1a.decider.pcs.duplicate(), Seq.empty, Seq.empty, Map.empty, Seq.empty, trigger)
              Success(Some(abd)) && Q(s1a, v1a)
          } {
            f => f
          }
        case Some(abdGoal: Exp) =>

          val tra = f.message.failureContexts.collectFirst {
            case SiliconAbductionFailureContext(trafo) if trafo.isDefined => trafo.get
          }

          val qPre = AbductionQuestion(s, v, Seq(abdGoal), stateAllowed = stateAllowed, trigger = trigger)
          val q = tra match {
            case Some(trafo) => trafo.f(qPre).asInstanceOf[AbductionQuestion]
            case _ => qPre
          }
          println(s"abdGoal $abdGoal due to $f \nin h:\n\t${s.h.values.mkString("\n\t")}\nand g:\n\t${s.g.values.mkString("\n\t")}")
          //println(s"and v:\n\t${v.decider.pcs.assumptions.mkString("\n\t")}")
          // NOTE: Without fractional permissions, the comment below is true
          // With fractional permissions, we HAVE to start with rule one because if we hold a fraction smaller
          // than the goal, we must subtract it from the goal
          //
          // We skip the first rule because we know that an error occured, so we cannot be done
          // This allows us to fold on null references multiple times, as is required for e.g. trees.
          AbductionApplier.applyRules(q){ //, currentRule = 1) {
            q1 =>
              //println(s"Completed abduction with state: \n\t${q1.s.h.values.mkString("\n\t")}")
              if (q1.goal.isEmpty) {
                val newState = q1.foundState.reverse
                val newStmts = q1.foundStmts

                if (q1.v.decider.checkSmoke()) {
                  Success(Some(BiAbductionFailure(s, v, initPcs)))
                  //Unreachable()
                } else {
                  val newChunks = newState.collect { case (_, c: Some[BasicChunk]) => c.get }
                  //val newOldHeaps = q1.s.oldHeaps.map { case (label, heap) => (label, heap + Heap(newChunks)) }
                  //val s1 = q1.s.copy(oldHeaps = newOldHeaps)
                  println(s"ABDUCTION TERMINATED IN \n\t\t${q1.s.h.values.mkString("\n\t\t")}")
                  println(s"\twith g: \n\t\t${q1.s.g.values.mkString("\n\t\t")}")
                  println(s"\twith v: \n\t\t${q1.v.decider.pcs.assumptions.mkString("\n\t\t")}")
                  println(s"\tWITH STATE ${newState}")
                  println(s"\tWITH STATEMENTS ${newStmts}")
                  val fieldChunks = newState.collect { case (fa: FieldAccessPredicate, c) => (c.get, fa.loc) }.toMap
                  println(s"\tFIELDCHUNKS: $fieldChunks")
                  val abd = AbductionSuccess(q1.s, q1.v, q1.v.decider.pcs.duplicate(), newState, newStmts, fieldChunks, newChunks, trigger)
                  Success(Some(abd)) && Q(q1.s, q1.v)
                }
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
      val absTransForm = VarTransformer(q1.s, q1.v, q1.s.g.values, q1.s.h)
      val res = absTransForm.transformState(q1.s)
      Q(q1.s, res, q1.v)
    }
  }

  def solveFraming(s: State, v: Verifier, pvef: Exp => PartialVerificationError, tra: VarTransformer, loc: Positioned, knownPosts: Seq[Exp], stateAllowed: Boolean)(Q: FramingSuccess => VerificationResult): VerificationResult = {

    //val tra = VarTransformer(s, v, targetVars, s.h)
    println(s"Will consume $knownPosts")
    executionFlowController.tryOrElse1[Option[Term]](s, v) { (s, v, QS) =>
      consumes(s, knownPosts, false, pvef, v)(QS)
    } { (s1: State, _: Option[Term], v1: Verifier) =>
      executionFlowController.locallyWithResult[Seq[Exp]](s1, v1) { (s1a, v1a, T) =>
        BiAbductionSolver.solveAbstraction(s1a, v1a) { (s2, framedPosts, v2) =>
          val newPosts = framedPosts.map { e => tra.transformExp(e) }.collect { case Some(e) => e }
          T(abductionUtils.sortExps(newPosts))
        }
      } {
        // We consumed all the posts and did not find any new ones. So create a fresh Framing Success with the bcs
        case Seq() =>
          Q(FramingSuccess(s1, v1, Seq(), loc, v.decider.pcs.duplicate(), tra)) // No new state or needed stmts
        // We consumed the post conditions and found new ones. Handle the new ones and add them to the result
        case newPosts1 =>
          solveFraming(s1, v1, pvef, tra, loc, newPosts1, stateAllowed) { frame =>
            val sortedPost = abductionUtils.sortExps(newPosts1)
            val newFrame = frame.copy(posts = frame.posts ++ sortedPost)
            Q(newFrame)
          }
      }
    } {
      // We failed to fulfill the posts. Perform abduction, add the results and try again.
      f =>println(s"Failed abstraction with $f")
        BiAbductionSolver.solveAbductionForError(s, v, f, stateAllowed, Some(loc))((s3, v3) => {
          solveFraming(s3, v3, pvef, tra, loc, knownPosts, stateAllowed)(Q)
        }
        )
    }
  }

  def resolveAbductionResults(m: Method, nf: NonFatalResult): Option[Method] = {
    val abdReses = abductionUtils.getAbductionSuccesses(nf)
    val newMatches = abdReses.flatMap(_.newFieldChunks).toMap
    val abdCases = abdReses.groupBy(res => (res.trigger.get.pos, res.stmts, res.state.map({ case (e, _) => e })))
    println(s"abdCases:")
    abdCases.foreach { case (key, values) =>
      println(s"-")
      values.foreach(v => println(s"\t\t$v [${v.pcs.branchConditions}]"))
    }
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
        (abdRes -> finalBcs)
    }
    // We want to add things in the reverse order of the abduction results.
    abdReses.reverse.foldLeft[Option[Method]](Some(m)) { (mOpt, res) =>
      mOpt match {
        case Some(m1) if joinedCases.contains(res) =>
          addToMethod(m1, Seq(joinedCases(res)), newMatches, res)
        case _ => mOpt
      }
    }
  }

  def addToMethod(m: Method, bcExps: Seq[Exp], newFieldChunks: Map[BasicChunk, LocationAccess], abdRes: AbductionSuccess): Option[Method] = {

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
      val newBody: Seqn = abdRes.trigger match {
        case None => body
        case Some(t: Stmt) if t == abductionUtils.dummyEndStmt =>
          addToInnerBody(body, finalStmt)

        case Some(t: Stmt) if abductionUtils.isEndOfLoopStmt(t) =>
          val loop = abductionUtils.getWhile(t.asInstanceOf[Label].invs.head, m)
          val newLoopBody = loop.body.copy(ss = loop.body.ss ++ finalStmt)(pos = loop.body.pos, info = loop.body.info, errT = loop.body.errT)
          val newLoop = loop.copy(body = newLoopBody)(loop.pos, loop.info, loop.errT)
          body.transform { case stmt if stmt == loop => newLoop }
        case Some(t: Stmt) =>
          body.transform {
            case stmt: Stmt if stmt == t && stmt.pos == t.pos =>
              Seqn(finalStmt :+ t, Seq())(t.pos, t.info, t.errT)
          }
        case Some(e: Exp) => body.transform {
          case ifStmt: If if ifStmt.cond == e && ifStmt.cond.pos == e.pos => Seqn(abdRes.stmts :+ ifStmt, Seq())(ifStmt.pos, ifStmt.info, ifStmt.errT)
          case whileStmt: While if whileStmt.cond == e && whileStmt.cond.pos == e.pos => Seqn(abdRes.stmts :+ whileStmt, Seq())(whileStmt.pos, whileStmt.info, whileStmt.errT)
        }
      }
      val newPres = abductionUtils.sortExps(abductionUtils.normalizePreconditions(m.pres ++ pres.get, s, v))
      Some(m.copy(pres = newPres, body = Some(newBody))(pos = m.pos, info = m.info, errT = m.errT))
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


  def resolveFramingResults(m: Method, nf: NonFatalResult): Option[Method] = {
    val frames = abductionUtils.getFramingSuccesses(nf)
    // We get a framing result for every branch.
    // So postconditions that are in every branch can just be added without any bcs
    val everyPosts = frames.head.posts.filter { p => frames.forall(_.posts.contains(p)) }
    //val formals = m.formalArgs.map(_.localVar) ++ m.formalReturns.map(_.localVar)
    //val bcs = frames.map(_.pcs.branchConditions)
    println(s"everyposts: $everyPosts")
    val cases = frames.map { f =>
      val prefVars = f.s.g.values.collect { case (var2, t) if m.formalArgs.map(_.localVar).contains(var2) => (var2, t) }
      val otherVars = f.s.g.values.collect { case (var2, t) if m.formalReturns.map(_.localVar).contains(var2) => (var2, t) }
      val bcs = f.pcs.branchConditions.flatMap {
        case terms.And(terms) => terms
        case term => Seq(term)
      }.distinct.filter(_ != True)
      (f.posts.diff(everyPosts), f.getBcExps(bcs, prefVars, otherVars))
    }.distinct
    println(s"cases: $cases")
    // We can remove bcs that hold in every branch
    val everyTerms = cases.head._2.filter { t => cases.forall(_._2.contains(t)) }

    val res = cases.collect {
      case (posts, bcs) if posts.nonEmpty && bcs.diff(everyTerms).nonEmpty => Implies(BigAnd(bcs.diff(everyTerms)), BigAnd(posts))()
      case (posts, _) if posts.nonEmpty => BigAnd(posts)
    } ++ everyPosts

    // we still need to sort the posts
    val sortedPosts = abductionUtils.sortExps(m.posts ++ res)
    val newM = m.copy(posts = sortedPosts)(pos = m.pos, info = m.info, errT = m.errT)
    Some(newM)

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

    // there is an issue here if the same loop is repeated twice in the same method
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
        case l: While if l.cond == loop.cond && l.cond.pos == loop.cond.pos =>
          val newInvs = abductionUtils.sortExps(inv ++ l.invs)
          l.copy(invs = newInvs)(pos = l.pos, info = l.info, errT = l.errT)
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

  val pve: PartialVerificationError = Internal()

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

  def normalizePreconditions(expressions: Seq[Exp], s: State, v: Verifier): Seq[Exp] = {
    val varTran = VarTransformer(s, v, s.g.values, s.h)

    def normalizePermissions(exp: Exp): Exp = {
      exp.transform({
        case fap: FieldAccessPredicate =>
          fap.copy(permExp = None)(fap.pos, fap.info, fap.errT)
        case pap: PredicateAccessPredicate =>
          pap.copy(permExp = None)(pap.pos, pap.info, pap.errT)
      })
    }

    def extractPerm(exp: Exp): Exp = exp match {
      case fap: FieldAccessPredicate         => fap.perm
      case pap: PredicateAccessPredicate     => pap.perm
      case Implies(_, fap: FieldAccessPredicate)     => fap.perm
      case Implies(_, pap: PredicateAccessPredicate) => pap.perm
      case e => e
    }

    expressions.groupBy(normalizePermissions).values.map { group =>
      if (group.size == 1) {
        group.head
      } else {
        val ap = group.head
        val permSum = group
          .map(extractPerm)
          .reduceLeft((p1, p2) => PermAdd(p1, p2)(p1.pos, p1.info, p1.errT))

        ap match {
          case fap: FieldAccessPredicate =>
            fap.copy(permExp = Some(permSum))(fap.pos, fap.info, fap.errT)
          case pap: PredicateAccessPredicate =>
            pap.copy(permExp = Some(permSum))(pap.pos, pap.info, pap.errT)
          case Implies(lhs, fap: FieldAccessPredicate) =>
            Implies(lhs, fap.copy(permExp = Some(permSum))(fap.pos, fap.info, fap.errT))(ap.pos, ap.info, ap.errT)
          case Implies(lhs, pap: PredicateAccessPredicate) =>
            Implies(lhs, pap.copy(permExp = Some(permSum))(pap.pos, pap.info, pap.errT))(ap.pos, ap.info, ap.errT)
          case other => other
        }
      }
    }.toSeq
  }


  def accWithPerm(ap: AccessPredicate, newPerm: Option[Exp]): AccessPredicate = {
    ap match {
      case fap: FieldAccessPredicate => FieldAccessPredicate(fap.loc, newPerm)(fap.pos, fap.info, fap.errT)
      case pap: PredicateAccessPredicate => PredicateAccessPredicate(pap.loc, newPerm)(pap.pos, pap.info, pap.errT)
    }
  }

  def asRational(p: Option[Exp]): Rational = p match {
    case Some(p2) => p2 match {
      case _: FullPerm => Rational(1, 1)
      case _: NoPerm => Rational(0, 1)
      case FractionalPerm(IntLit(l), IntLit(r)) => Rational(l, r)
      case PermMul(e1, e2) => asRational(Some(e1)) * asRational(Some(e2))
      case PermSub(e1, e2) => asRational(Some(e1)) - asRational(Some(e2))
      case PermAdd(e1, e2) => asRational(Some(e1)) + asRational(Some(e2))
      case PermDiv(e1, e2) => asRational(Some(e1)) / asRational(Some(e2))
      case PermPermDiv(e1, e2) => asRational(Some(e1)) / asRational(Some(e2))
      case WildcardPerm() => Rational(0, 1)
      case e =>
        throw new IllegalStateException(s"Impossible by invariant: $p")
    }
    case None => Rational(1, 1)
  }

  def asPerm(r: Rational): Exp = {
    FractionalPerm(IntLit(r.numerator)(), IntLit(r.denominator)())()
  }

  // This does max(a - b, 0)
  def clampSubPerm(a: Option[Exp], b: Option[Exp]): FractionalPerm = {
    val sub = asRational(a) - asRational(b)
    FractionalPerm(
      IntLit(if (sub.compare(Rational(0, 1)) < 0) 0 else sub.numerator)(),
      IntLit(sub.denominator)()
    )()
  }

  def maxPerm(p1: Exp, p2: Exp, v: Verifier, varTran: VarTransformer): Exp = {
    (p1, p2) match {
      case (Implies(lhs1, inner1), Implies(lhs2, inner2)) if lhs1 == lhs2 =>
        val term1 = varTran.permExpToTerm(inner1 match { case fap: FieldAccessPredicate => fap.perm case pap: PredicateAccessPredicate => pap.perm })
        val term2 = varTran.permExpToTerm(inner2 match { case fap: FieldAccessPredicate => fap.perm case pap: PredicateAccessPredicate => pap.perm })
        if (v.decider.check(terms.AtLeast(term1, term2), Verifier.config.checkTimeout())) p1 else p2
      case (Implies(_, _), _) | (_, Implies(_, _)) =>
        p1
      case _ =>
        val term1 = varTran.permExpToTerm(p1)
        val term2 = varTran.permExpToTerm(p2)
        if (v.decider.check(terms.AtLeast(term1, term2), Verifier.config.checkTimeout())) p1 else p2
    }
  }

  def minPerm(p1: Exp, p2: Exp, v: Verifier, varTran: VarTransformer): Exp = {
    (p1, p2) match {
      case (Implies(lhs1, inner1), Implies(lhs2, inner2)) if lhs1 == lhs2 =>
        val term1 = varTran.permExpToTerm(inner1 match { case fap: FieldAccessPredicate => fap.perm case pap: PredicateAccessPredicate => pap.perm })
        val term2 = varTran.permExpToTerm(inner2 match { case fap: FieldAccessPredicate => fap.perm case pap: PredicateAccessPredicate => pap.perm })
        if (v.decider.check(terms.AtMost(term1, term2), Verifier.config.checkTimeout())) p1 else p2
      case (Implies(_, _), _) | (_, Implies(_, _)) =>
        p1
      case _ =>
        val term1 = varTran.permExpToTerm(p1)
        val term2 = varTran.permExpToTerm(p2)
        if (v.decider.check(terms.AtMost(term1, term2), Verifier.config.checkTimeout())) p1 else p2
    }
  }

  def maxPermRational(a: Option[Exp], b: Option[Exp]): Rational = {
    val aRational = asRational(a)
    val bRational = asRational(b)
    if (aRational.compare(bRational) >= 0) aRational else bRational
  }

  def minPermRational(a: Option[Exp], b: Option[Exp]): Rational = {
    val aRational = asRational(a)
    val bRational = asRational(b)
    if (aRational.compare(bRational) < 0) aRational else bRational
  }

  def fieldsMap(pred: Predicate, a: PredicateAccessPredicate): Map[FieldAccess, Rational] = {
    pred.body.get.transform {
      case lc: AbstractLocalVar if pred.formalArgs.head.localVar == lc => a.loc.args.head
    }.collect {
      case fap: FieldAccessPredicate => fap.permExp match {
        case None                    => fap.loc -> Rational(1, 1)
        case Some(_: FullPerm)       => fap.loc -> Rational(1, 1)
        case Some(_: NoPerm)         => fap.loc -> Rational(0, 1)
        case Some(FractionalPerm(IntLit(a), IntLit(b))) => fap.loc -> Rational(a, b)
      }
    }.filter { case (fa, _) =>
      // We need ot filter out things like curr.next.prev
      !fa.rcv.isInstanceOf[FieldAccess]
    }.toMap
  }

  // If the wand contains acc(list(x)) the structure has ", write" instead of ", Perm",
  // need to correct it to semantically compare wands with fractions
  def correctStructure(structure: MagicWandStructure.MagicWandStructure): MagicWandStructure.MagicWandStructure = {
    def transPerm(perm: Option[Exp], fap: AccessPredicate) = Some(perm match {
      case None => LocalVar ("Perm", Perm)(fap.pos, fap.info, fap.errT)
      case Some(_: FullPerm) => LocalVar ("Perm", Perm)(fap.pos, fap.info, fap.errT)
      case Some(p) => p
    })
    structure.transform{
      case fap@FieldAccessPredicate(loc, perm) =>
        FieldAccessPredicate(loc, transPerm(perm, fap))(fap.pos, fap.info, fap.errT)
      case pap@PredicateAccessPredicate(loc, perm) =>
        PredicateAccessPredicate(loc, transPerm(perm, pap))(pap.pos, pap.info, pap.errT)
    }
  }

  def checkChunk(loc: LocationAccess, s: State, v: Verifier, lostAccesses: Map[Exp, Term])
                          (Q: Option[BasicChunk] => VerificationResult): VerificationResult = {
    val arg = loc match {
      case FieldAccess(rcv, _) => rcv
      case PredicateAccess(args, _) => args.head
    }
    safeEval(arg, s, v, lostAccesses) { (s2, terms, v2) =>
      terms match {
        case Some(term) =>
          val resource = loc.res(s2.program)
          val id = ChunkIdentifier(resource, s2.program)
          val chunk = findChunk[BasicChunk](s2.h.values, id, Seq(term), v2)
          Q(chunk)
        case None => Q(None)
      }
    }
  }

  /**
   * Does a couple of things to ensure evalution works properly:
   *
   * Check the lost accesses to see if the access is there
   * Evaluate sub-expressions safely to ensure that a missing chunk will not cause the evaluation to silently abort
   */
  def safeEval(e: Exp, s: State, v: Verifier, lostAccesses: Map[Exp, Term])
                        (Q: (State, Option[Term], Verifier) => VerificationResult): VerificationResult = {

    if (!e.contains[LocationAccess]) {
      eval(s, e, pve, v)((s1, t, _, v1) => Q(s1, Some(t), v1))
    } else {

      // If the arg was lost, we have it in the map
      if (lostAccesses.contains(e)) {
        Q(s, Some(lostAccesses(e)), v)
      } else {
        e match {
          // If the arg is a location access, we have to recursively check it
          case loc: LocationAccess => checkChunk(loc, s, v, lostAccesses) {
            case Some(c) => Q(s, Some(c.snap), v)
            case None => Q(s, None, v)
          }
          //case lv: AbstractLocalVar => Q(s, Some(s.g(lv)), v)
          case _ => eval(s, e, pve, v)((s, t, _, v) => Q(s, Some(t), v))
          //case _ => evalLocationAccess(q.s, loc, pve, q.v) { (s2, _, tArgs, v2) => Q(s2, Some(tArgs), v2) }
        }
      }
    }
  }

  def permsTo(loc: LocationAccess, s: State, v: Verifier, lostAccesses: Map[Exp, Term])
                       (Q: Option[Exp] => VerificationResult) = {
    val arg = loc match {
      case FieldAccess(rcv, _) => rcv
      case PredicateAccess(args, _) => args.head
    }

    safeEval(arg, s, v, lostAccesses) { (s2, terms, v2) =>
      terms match {
        case Some(term) =>
          val resource = loc.res(s2.program)
          val id = ChunkIdentifier(resource, s2.program)
          val chunkOpt = findChunk[BasicChunk](s2.h.values, id, Seq(term), v2)
          chunkOpt match {
            case None => Q(Some(NoPerm()()))
            case Some(chunk) =>
              val varTran = VarTransformer(s, v, s.g.values, s.h)
              // TODO: Maybe here transform the permTerm?
              Q(varTran.transformTerm(chunk.perm))
          }
        case None => Q(Some(NoPerm()()))
      }
    }
  }

  def expMatchWithPermissions(exp1: Exp, exp2: Exp, v: Verifier, varTran: VarTransformer): Boolean = {
    (exp1, exp2) match {
      case (fap1: FieldAccessPredicate, fap2: FieldAccessPredicate) =>
        println(s"${fap1.permExp}, ${fap2.permExp}")
        fap1.loc == fap2.loc &&
          ((fap1.permExp, fap2.permExp) match {
          case (Some(perm1), Some(perm2)) =>
            v.decider.check(terms.Equals(varTran.permExpToTerm(perm1), varTran.permExpToTerm(perm2)), Verifier.config.checkTimeout())
          case (None, None) => true
          case (None, Some(FullPerm())) => true
          case (Some(FullPerm()), None) => true
          case _ => false
        })
      case (pap1: PredicateAccessPredicate, pap2: PredicateAccessPredicate) =>
        println(s"${pap1.permExp}, ${pap2.permExp}")
        pap1.loc == pap2.loc &&
          ((pap1.permExp, pap2.permExp) match {
            case (Some(perm1), Some(perm2)) =>
              v.decider.check(terms.Equals(varTran.permExpToTerm(perm1), varTran.permExpToTerm(perm2)), Verifier.config.checkTimeout())
            case (None, None) => true
            case (None, Some(FullPerm())) => true
            case (Some(FullPerm()), None) => true
            case _ => false
          })
      case _ => false
    }
  }

  def simplifyPermission(e: Exp): Exp = {
    if (!e.isInstanceOf[PermExp] || e.isInstanceOf[WildcardPerm]) return e
    val rational = abductionUtils.asRational(Some(e))
    if (rational.numerator == 1 && rational.denominator == 1) {
      FullPerm()()
    } else if (rational.numerator == 0) {
      NoPerm()()
    } else {
      FractionalPerm(IntLit(rational.numerator)(), IntLit(rational.denominator)())()
    }
  }

  def concretizeAccs(accs: Seq[AccessPredicate], q: AbductionQuestion)
                    (Q: Seq[AccessPredicate] => VerificationResult): VerificationResult = {
    def go(remaining: List[AccessPredicate],
           accumulated: List[AccessPredicate]): VerificationResult = {
      remaining match {
        case Nil =>
          Q(accumulated.reverse)

        case (fap@FieldAccessPredicate(_, Some(WildcardPerm()))) :: tail =>
          go(tail, abductionUtils.accWithPerm(fap, Some(FractionalPerm(IntLit(1)(), IntLit(4)())())) :: accumulated)
        /*findMinPerm(loc, q.s, q.v, q.lostAccesses) { permOpt =>
          val perm = permOpt.getOrElse(FullPerm()())
          go(tail, abductionUtils.accWithPerm(fap, Some(perm)) :: accumulated)
        }*/

        case (pap@PredicateAccessPredicate(_, Some(WildcardPerm()))) :: tail =>
          go(tail, abductionUtils.accWithPerm(pap, Some(FractionalPerm(IntLit(1)(), IntLit(4)())())) :: accumulated)
        /*findMinPerm(loc, q.s, q.v, q.lostAccesses) { permOpt =>
          val perm = permOpt.getOrElse(FullPerm()())
          go(tail, abductionUtils.accWithPerm(pap, Some(perm)) :: accumulated)
        }*/

        case acc :: tail =>
          acc match {
            case g @ AccessPredicate(loc: LocationAccess, permG) =>
              abductionUtils.permsTo(loc, q.s, q.v, q.lostAccesses) { permH =>
                val newP = abductionUtils.clampSubPerm(Some(permG), permH)
                val g2   = abductionUtils.accWithPerm(g, Some(newP))
                go(tail, g2 :: accumulated)
              }

            /*case _ =>
              go(tail, acc :: accumulated)*/
          }
      }
    }

    go(accs.toList, Nil)
  }

  def buildPredicatePermissionsMap(s: State, v: Verifier): Map[Predicate, Map[Object, FractionalPerm]] = {

    var result: Map[Predicate, Map[Object, FractionalPerm]] = Map.empty

    def processLocation(bS: State, bV: Verifier, eS: State, loc: LocationAccess)
                       (Q: FractionalPerm => VerificationResult): VerificationResult = {

      abductionUtils.permsTo(loc, eS, v, Map.empty) { prevPerm =>
        abductionUtils.permsTo(loc, bS, bV, Map.empty) { currPerm =>
          val gainedPerm = abductionUtils.clampSubPerm(currPerm, prevPerm)
          Q(gainedPerm)
        }
      }

    }

    def processPredicates(remaining: List[Predicate], acc: Map[Predicate, Map[Object, FractionalPerm]]): VerificationResult = remaining match {
      case Nil =>
        result = acc
        Success()
      case pred :: rest =>
        processPredicate(pred) { locationPermMap =>
          processPredicates(rest, acc + (pred -> locationPermMap))
        }
    }

    def processPredicate(pred: Predicate)
                        (Q: Map[Object, FractionalPerm] => VerificationResult): VerificationResult = {

      def innermostFA(loc: LocationAccess): Option[FieldAccess] = loc match {
        case fa @ FieldAccess(rcv, _) =>
          rcv match {
            case innerRcv: FieldAccess => innermostFA(innerRcv)
            case _ => Some(fa)
          }
        case _ => None
      }

      val locations: Seq[LocationAccess] = pred.body.get.flatMap {
        case PredicateAccessPredicate(loc, _) => Some(loc)
        case FieldAccessPredicate(loc, _) => innermostFA(loc)
        case _ => None
      }.toSeq.distinct

      val freshVars = pred.formalArgs.map(arg => LocalVar(arg.name, arg.typ)())
      val varDecls = freshVars.map {
        fv => LocalVarDeclStmt(LocalVarDecl(fv.name, fv.typ)())()
      }

      // Helper to merge two maps taking max permission for each key
      def mergeMaxPerms(acc1: Map[Object, FractionalPerm],
                        acc2: Map[Object, FractionalPerm]): Map[Object, FractionalPerm] = {
        val allKeys = acc1.keySet ++ acc2.keySet
        allKeys.map { key =>
          val perm1 = acc1.get(key).orElse(Some(NoPerm()()))
          val perm2 = acc2.get(key).orElse(Some(NoPerm()()))
          val maxP = abductionUtils.maxPermRational(perm1, perm2)
          key -> FractionalPerm(IntLit(maxP.numerator)(), IntLit(maxP.denominator)())()
        }.toMap
      }

      var accumulatedPerms: Map[Object, FractionalPerm] = Map.empty

      def processLocations(bS: State, bV: Verifier, eS: State, remaining: Seq[LocationAccess], acc: Map[Object, FractionalPerm]): VerificationResult = remaining match {
        case Nil =>
          accumulatedPerms = mergeMaxPerms(accumulatedPerms, acc)
          Success()
        case loc :: rest =>
          processLocation(bS, bV, eS, loc) { perm =>
            loc match {
              case PredicateAccess(_, name) => processLocations(bS, bV, eS, rest, acc + (name -> perm))
              case FieldAccess(_, field) => processLocations(bS, bV, eS, rest, acc + (field -> perm))
            }
          }
      }

      val result = executor.exec(s, Seqn(varDecls, Seq.empty)(), v) { (eS, _) =>
        executor.exec(s, Seqn(varDecls :+ Inhale(pred.body.get)(), Seq.empty)(), v) { (bS, bV) =>
          processLocations(bS, bV, eS, locations, Map.empty)
        }
      }

      result && Q(accumulatedPerms)
    }

    processPredicates(s.program.predicates.toList, Map.empty)
    result
  }

  /*def retryOnFailedAssertion(
                                 s: State,
                                 v: Verifier,
                                 exec: (State, Verifier, (State, Verifier) => VerificationResult) => VerificationResult
                               )(Q: (State, Verifier) => VerificationResult): VerificationResult = {
    executionFlowController.tryOrElse0(s, v) { (s1, v1, T) =>
      exec(s1, v1, T)
    } {
      (s1a, v1a) =>
        println(s"Attempt successful")
        Q(s1a, v1a)
    } {
      f =>
        f.message.reason match {
          case AssertionFalse(assertion) =>
            println(s"exec failed with ${f.message.reason}")
            producer.produce(s, freshSnap, assertion, pve, v) { (s1r, v1r) =>
              println(s"Produced, will reattempt")
              retryOnFailedAssertion(s1r, v1r, exec)(Q)
            }
          case _ =>
            f
        }
    }
  }*/

  def pickBranch(
                  results: Seq[AbductionSuccess]
                ): Seq[AbductionSuccess] = {
    val grouped = results.groupBy(_.pcs.branchConditions)
    if (grouped.isEmpty) return Seq.empty

    val minSize = grouped.keys.map(_.size).min
    var current = grouped.filter(_._1.size == minSize).maxBy(_._2.size)._1
    val selectedBcs = collection.mutable.Set(current)

    var searching = true
    while (searching) {
      val extensions = grouped.filter { case (bcs, _) =>
        bcs.size == current.size + 1 && bcs.tail == current
      }
      if (extensions.isEmpty) {
        searching = false
      } else {
        val (nextBcs, _) = extensions.maxBy(_._2.size)
        selectedBcs += nextBcs
        current = nextBcs
      }
    }

    results.filter(r => selectedBcs.contains(r.pcs.branchConditions))
  }

}
