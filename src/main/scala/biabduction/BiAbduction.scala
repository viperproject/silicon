package viper.silicon.biabduction

import viper.silicon.decider.PathConditionStack
import viper.silicon.interfaces.{Failure, NonFatalResult, Success, VerificationResult}
import viper.silicon.rules.executionFlowController
import viper.silicon.state._
import viper.silicon.state.terms.Term
import viper.silicon.utils.ast.BigAnd
import viper.silicon.verifier.Verifier
import viper.silver.ast._
import viper.silver.verifier.errors.Internal
import viper.silver.verifier.{AbductionQuestionTransformer, DummyReason, PartialVerificationError, VerificationError}

trait BiAbductionResult {
  def s: State

  def v: Verifier

}

trait BiAbductionSuccess extends BiAbductionResult {
  def loc: Position

  val line: String = loc match {
    case sp: SourcePosition => sp.start.line.toString
    case lc: HasLineColumn => lc.line.toString
    case pos => pos.toString
  }
}

case class AbductionSuccess(s: State, v: Verifier, pcs: PathConditionStack, state: Seq[Exp] = Seq(), stmts: Seq[Stmt] = Seq(), loc: Position) extends BiAbductionSuccess {

  override def toString: String = {
    "Successful abduction at line " + line + ":\n" + "Abduced state\n" + state.map(_.toString()).mkString("\n") + "\nAbduced statements\n" + stmts.reverse.map(_.toString()).mkString("\n")
  }

  def toPrecondition(preVars: Map[AbstractLocalVar, Term], preHeap: Heap, ignoredBcs: Seq[Exp] = Seq()): Option[Seq[Exp]] = {

    // We have to use the pcs from the abduction point
    val prevPcs = v.decider.pcs
    v.decider.setPcs(pcs)
    val varTrans = VarTransformer(s, v, preVars, preHeap)
    val presTransformed = state.map {
      varTrans.transformExp
    }

    if (presTransformed.contains(None)) { // We could not express the state as a precondition
      None
    } else {
      // TODO There is a common case where we add x != null because we know acc(x.next). We want to remove this bc
      // If performing the abduction somehow introduces branches, then this could cause problems here.
      // TODO for loops, we would like to remove the loop condition from conditions we find. How do we do that?
      // Can we "subtract" the pathconditions from the original state somehow?
      //val bcs = v.decider.pcs.branchConditionExps.collect { case Some(e) if varTrans.transformExp(e).isDefined && e != TrueLit()() && !ignoredBcs.contains(e)  }.toSet
      val bcs = v.decider.pcs.branchConditions.map { term => varTrans.transformTerm(term) }
        .collect {
          case Some(e) if e != TrueLit()() && !ignoredBcs.contains(e) && !ignoredBcs.contains(varTrans.transformExp(e).get) => varTrans.transformExp(e).get
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
}

case class LoopInvariantSuccess(s: State, v: Verifier, invs: Seq[Exp] = Seq(), loc: Position) extends BiAbductionSuccess {
  override def toString: String = "Successful loop invariant abduction"
}

case class FramingSuccess(s: State, v: Verifier, posts: Seq[Exp], loc: Position) extends BiAbductionSuccess {
  override def toString: String = "Successful framing"

}

case class BiAbductionFailure(s: State, v: Verifier) extends BiAbductionResult {
  override def toString: String = "Abduction failed"
}

trait RuleApplier[S] {

  protected val rules: Seq[BiAbductionRule[S]]

  /**
    * Recursively applies the rules until we reach the end of the rules list.
    */
  def apply(in: S, currentRule: Int = 0): S = {

    var result = in

    if (currentRule < rules.length) {
      rules(currentRule).apply(in) { s =>
        s match {
          case Some(out) =>
            result = apply(out)
          case None =>
            result = apply(in, currentRule + 1)
        }
        Failure(Internal().dueTo(DummyReason))
      }
    }
    result
  }
}

trait BiAbductionRule[S] {

  val pve: PartialVerificationError = Internal()
  val ve: VerificationError = pve.dueTo(DummyReason)

  def apply(q: S)(Q: Option[S] => VerificationResult): VerificationResult

}

object BiAbductionSolver {

  def solveAbduction(s: State, v: Verifier, goal: Seq[Exp], tra: Option[AbductionQuestionTransformer], loc: Position): BiAbductionResult = {

    executionFlowController.locally(s, v)((s1, v1) => {

      val qPre = AbductionQuestion(s1, v1, goal)

      val q = tra match {
        case Some(trafo) => trafo.f(qPre).asInstanceOf[AbductionQuestion]
        case _ => qPre
      }

      val q1 = AbductionApplier.apply(q)

      if (q1.goal.isEmpty) {
        Success(Some(AbductionSuccess(q.s, q.v, q.v.decider.pcs.duplicate(), q1.foundState, q1.foundStmts, loc = loc)))
      } else {
        Failure(Internal() dueTo DummyReason)
      }
    }) match {
      case Success(Some(abd: AbductionSuccess)) => abd
      case _ => BiAbductionFailure(s, v)
    }
  }

  def solveAbstraction(s: State, v: Verifier, exps: Seq[Exp]): Seq[Exp] = {
    var res: Seq[Exp] = Seq()
    executionFlowController.locally(s, v)((s1, v1) => {
      val q = AbstractionQuestion(exps, s1, v1)
      res = AbstractionApplier.apply(q).exps
      Success()
    })
    res
  }

  def solveFraming(s: State, v: Verifier, postVars: Map[AbstractLocalVar, Term], loc: Position = NoPosition, ignoredBcs: Seq[Exp] = Seq()): FramingSuccess = {

    val tra = VarTransformer(s, v, postVars, s.h)
    val res = s.h.values.collect { case c: BasicChunk => tra.transformChunk(c) }.collect { case Some(e) => e }.toSeq
    val bcs = v.decider.pcs.branchConditions.map { term => tra.transformTerm(term) }.collect { case Some(e) if e != TrueLit()() && !ignoredBcs.contains(e) => e }.toSet
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
  // TODO We currently assume that there is only one predicate and one field
  def getPredicate(p: Program, rec: Exp, perm: Exp = FullPerm()()): PredicateAccessPredicate = {
    PredicateAccessPredicate(PredicateAccess(Seq(rec), p.predicates.head.name)(), perm)()
  }

  def getNextAccess(p: Program, rec: Exp, perm: Exp = FullPerm()()): FieldAccessPredicate = {
    FieldAccessPredicate(FieldAccess(rec, p.fields.head)(), perm)()
  }

  def getVars(t: Term, g: Store): Seq[AbstractLocalVar] = {
    g.values.collect({ case (v, t1) if t1 == t => v }).toSeq
  }

  def getField(name: BasicChunkIdentifier, p: Program) = {
    p.fields.find(_.name == name.name).get
  }

  def getAbductionResults(vr: NonFatalResult): Seq[AbductionSuccess] = {
    (vr +: vr.previous).collect { case Success(Some(abd: AbductionSuccess)) => abd }
  }

  def getFramingSuccesses(vr: NonFatalResult): Seq[FramingSuccess] = {
    (vr +: vr.previous).collect { case Success(Some(framing: FramingSuccess)) => framing }
  }

  def getInvariantSuccesses(vr: NonFatalResult): Seq[LoopInvariantSuccess] = {
    (vr +: vr.previous).collect { case Success(Some(inv: LoopInvariantSuccess)) => inv }
  }
}


