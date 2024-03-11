package viper.silicon.biabduction

import viper.silicon.interfaces.{Failure, VerificationResult}
import viper.silicon.state._
import viper.silicon.state.terms.Term
import viper.silicon.utils.ast.BigAnd
import viper.silicon.verifier.Verifier
import viper.silver.ast._
import viper.silver.verifier.errors.Internal
import viper.silver.verifier.{AbductionQuestionTransformer, DummyReason, PartialVerificationError, VerificationError}

// TODO we want to continue execution if we abduce successfully. Idea:
// - Hook into the "Try or Fail" methods
// - Instead of actually failing, do bi-abduction
// - track the results somewhere
// - produce the precondition, execute the statements, and continue execution
// - At the end, do abstraction on all the found preconditions. Find the necessary statements for the abstractions

trait AbductionResult

case class AbductionSuccess(pre: Seq[Exp] = Seq(), stmts: Seq[Stmt] = Seq(), posts: Seq[Exp] = Seq(), invs: Seq[Exp] = Seq()) extends AbductionResult {
  override def toString: String = {
    "Abduced preconditions\n" + pre.map(_.toString()).mkString("\n") + "\nAbduced statements\n" + stmts.map(_.toString()).mkString("\n")
  }
}

case class AbductionFailure() extends AbductionResult {
  override def toString: String = "Abduction failed"

}


object BiAbductionSolver {

  def solve(s: State, v: Verifier, goal: Seq[Exp], tra: Option[AbductionQuestionTransformer]): AbductionResult = {

    val qPre = SiliconAbductionQuestion(s, v, goal)

    val q = tra match {
      case Some(trafo) => trafo.f(qPre).asInstanceOf[SiliconAbductionQuestion]
      case _ => qPre
    }

    val ins = s.currentMember match {
      case Some(m: Method) => m.formalArgs.map(_.localVar)
      case _ => Seq()
    }
    val varTrans = VarTransformer(q.s, q.v, ins)

    val q1 = AbductionApplier.apply(q)

    if (q1.goal.isEmpty) {

      // TODO it is possible that we want to transform variable in a non-strict way before abstraction
      val pres = AbstractionApplier.apply(AbstractionQuestion(q1.foundPrecons, q1.s.program)).exps

      // TODO if some path conditions already contain Ands, then we might reject clauses that we could actually handle
      val bcs = q1.v.decider.pcs.branchConditionExps.collect { case Some(e) if varTrans.transformExp(e).isDefined => varTrans.transformExp(e).get }

      // TODO Weak transformation of statements to original variables (Viper encoding can introduce new variables)

      val presTransformed = pres.map { (e: Exp) =>
        varTrans.transformExp(e) match {
          case Some(e1) => e1
          case _ => e
        }
      }.map { e =>
        bcs match {
          case Seq() => e
          case _ => Implies(BigAnd(bcs), e)()
        }
      }
      AbductionSuccess(presTransformed, q1.foundStmts)

    } else {
      AbductionFailure()
    }
  }

  def generatePostconditions(s: State, v: Verifier): AbductionSuccess = {

    val formals = s.currentMember match {
      case Some(m: Method) => m.formalArgs.map(_.localVar) ++ m.formalReturns.map(_.localVar)
      case _ => Seq()
    }
    val tra = VarTransformer(s, v, formals)
    val res = s.h.values.collect { case c: BasicChunk => tra.transformChunk(c) }.collect { case Some(e) => e }.toSeq

    val absRes = AbstractionApplier.apply(AbstractionQuestion(res, s.program)).exps
    AbductionSuccess(posts = absRes)
    //"Abduced postconditions\n" + absRes.map(_.toString()).mkString("\n")
  }
}

trait RuleApplier[S] {

  protected val rules: Seq[BiAbductionRule[S, _]]

  /**
    * Recursively applies the rules until we reach the end of the rules list.
    */
  def apply(in: S, currentRule: Int = 0): S = {

    var result = in

    rules(currentRule).checkAndApply(in, currentRule)((in1, r1) => {
      if (r1 == rules.length) {
        result = in1
      } else {
        result = apply(in1, r1)
      }
      Failure(Internal().dueTo(DummyReason))
    })
    result
  }
}

trait BiAbductionRule[S, T] {

  val pve: PartialVerificationError = Internal()
  val ve: VerificationError = pve.dueTo(DummyReason)

  def checkAndApply(q: S, rule: Int)(Q: (S, Int) => VerificationResult): VerificationResult = {
    check(q) {
      case Some(e) => apply(q, e)(Q(_, 0))
      case None => Q(q, rule + 1)
    }
  }

  protected def check(q: S)(Q: Option[T] => VerificationResult): VerificationResult

  protected def apply(q: S, inst: T)(Q: S => VerificationResult): VerificationResult

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
}


