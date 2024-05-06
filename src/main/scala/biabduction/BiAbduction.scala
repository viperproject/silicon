package viper.silicon.biabduction

import viper.silicon.interfaces.{Failure, VerificationResult}
import viper.silicon.state._
import viper.silicon.state.terms.Term
import viper.silicon.utils.ast.BigAnd
import viper.silicon.verifier.Verifier
import viper.silver.ast
import viper.silver.ast._
import viper.silver.verifier.errors.Internal
import viper.silver.verifier.{AbductionQuestionTransformer, DummyReason, PartialVerificationError, VerificationError}

// TODO we want to continue execution if we abduce successfully. Idea:
// - Hook into the "Try or Fail" methods
// - Instead of actually failing, do bi-abduction
// - track the results somewhere
// - produce the precondition, execute the statements, and continue execution
// - At the end, do abstraction on all the found preconditions. Find the necessary statements for the abstractions

trait BiAbductionResult {
  def s: State

  def v: Verifier
}

trait BiAbductionSuccess extends BiAbductionResult

case class AbductionSuccess(s: State, v: Verifier, pre: Seq[Exp] = Seq(), stmts: Seq[Stmt] = Seq(), loc: Position) extends BiAbductionSuccess {
  override def toString: String = {

    val line = loc match {
      case sp: ast.SourcePosition => sp.start.line
      case lc: ast.HasLineColumn => lc.line
    }
    "Successful abduction at line " + line.toString + ":\n" + "Abduced preconditions\n" + pre.map(_.toString()).mkString("\n") + "\nAbduced statements\n" + stmts.reverse.map(_.toString()).mkString("\n")
  }
}

case class LoopInvariantSuccess(s: State, v: Verifier, invs: Seq[Exp] = Seq(), stmts: Seq[Stmt] = Seq()) extends BiAbductionSuccess {
  override def toString: String = "Successful loop invariant abduction"
}

case class FramingSuccess(s: State, v: Verifier, posts: Seq[Exp]) extends BiAbductionSuccess

case class BiAbductionFailure(s: State, v: Verifier) extends BiAbductionResult {
  override def toString: String = "Abduction failed"
}


object BiAbductionSolver {

  def solveAbduction(s: State, v: Verifier, goal: Seq[Exp], tra: Option[AbductionQuestionTransformer], loc: Position): BiAbductionResult = {

    val qPre = SiliconAbductionQuestion(s, v, goal)

    val q = tra match {
      case Some(trafo) => trafo.f(qPre).asInstanceOf[SiliconAbductionQuestion]
      case _ => qPre
    }

    val ins = q.s.currentMember match {
      case Some(m: Method) => m.formalArgs.map(_.localVar)
      case _ => Seq()
    }

    val varTrans = VarTransformer(q.s, q.v, q.s.g.values.collect { case (v: AbstractLocalVar, t: Term) if ins.contains(v) => (v, t)}, q.s.oldHeaps.head._2)

    val q1 = AbductionApplier.apply(q)

    if (q1.goal.isEmpty) {

      // TODO it is possible that we want to transform variable in a non-strict way before abstraction
      val pres = AbstractionApplier.apply(AbstractionQuestion(q1.foundPrecons, q1.s.program)).exps

      // TODO There is a common case where we add x != null because we know acc(x.next). We want to remove this bc
      val bcs = q1.v.decider.pcs.branchConditionExps.collect { case Some(e) if varTrans.transformExp(e).isDefined && e != TrueLit()() => varTrans.transformExp(e).get }.toSet

      // TODO Weak transformation of statements to original variables (Viper encoding can introduce new variables)
      val presTransformed = pres.map { varTrans.transformExp }

      if (presTransformed.contains(None)) {
        BiAbductionFailure(q1.s, q1.v)
      } else {
        val presFinal = presTransformed.map { e =>
          if(bcs.isEmpty){
            e.get
          } else {
            Implies(BigAnd(bcs), e.get)()
          }
        }
        AbductionSuccess(q1.s, q1.v, presFinal, q1.foundStmts, loc = loc)
      }
    } else {
      BiAbductionFailure(q1.s, q1.v)
    }
  }

  def solveFraming(s: State, v: Verifier): FramingSuccess = {

    val formals = s.currentMember match {
      case Some(m: Method) => m.formalArgs.map(_.localVar) ++ m.formalReturns.map(_.localVar)
      case _ => Seq()
    }
    val tra = VarTransformer(s, v, s.g.values.filter(formals.contains), s.h)
    val res = s.h.values.collect { case c: BasicChunk => tra.transformChunk(c) }.collect { case Some(e) => e }.toSeq

    val absRes = AbstractionApplier.apply(AbstractionQuestion(res, s.program)).exps
    FramingSuccess(s, v, posts = absRes)
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
      case Some(e) =>
        println("Applied rule " + this.getClass.getSimpleName)
        apply(q, e)(Q(_, 0))
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


