package viper.silicon.biabduction

import biabduction.{AbstractionApply, AbstractionJoin, AbstractionListFold, AbstractionListPackage}
import viper.silicon.interfaces.{Failure, VerificationResult}
import viper.silicon.resources.FieldID
import viper.silicon.state.terms.Term
import viper.silicon.state.{BasicChunk, BasicChunkIdentifier, State, Store}
import viper.silicon.utils.ast.BigAnd
import viper.silicon.verifier.Verifier
import viper.silver.ast.{AbstractLocalVar, And, EqCmp, Exp, FieldAccess, FieldAccessPredicate, Implies, LocalVar, MagicWand, Method, NeCmp, Not, NullLit, PredicateAccess, PredicateAccessPredicate, Stmt, TrueLit}
import viper.silver.verifier.{AbductionQuestion, DummyReason, PartialVerificationError}
import viper.silver.verifier.errors.Internal

object AbductionSolver {

  private val abductionRules = Seq(AbductionRemove, AbductionMatch, AbductionListFoldBase, AbductionListFold, AbductionListUnfold, AbductionMissing)
  private val abstractionRules = Seq(AbstractionListFold, AbstractionListPackage, AbstractionJoin, AbstractionApply)
  def solve(q: SiliconAbductionQuestion): String = {
    val fail = Failure(Internal().dueTo(DummyReason))
    var result = ""


    applyRule(q, 0) { q1 => {
      if (q1.goal.isEmpty) {

        val bcs = BigAnd(q.v.decider.pcs.branchConditionExps.collect { case Some(e) if q.transformToInputs(e).isDefined => q.transformToInputs(e).get })

        val rt = q1.foundPrecons.map { (e: Exp) =>
          (q.transformToInputs(e), bcs) match {
            case (Some(e1), TrueLit()) => e1.toString()
            case (Some(e1), bcs) => Implies(bcs, e1)().toString()
            case _ => "Could not be transformed to inputs: " + e.toString()
          }
        }.mkString("\n")
        result = "Abduction successful.\nAbduced preconditions:\n" + rt + "\nAbduced statements:\n" + q1.foundStmts.map(_.toString()).mkString("\n")
      } else {
        result = "Abduction failed."
      }
      fail
    }
    }
    result
  }

  /**
    * Recursively applies the abduction rules until we reach the end of the rules list. If the goal is empty, we were
    * successful.
    */
  private def applyRule(q: SiliconAbductionQuestion, rule: Int)(Q: SiliconAbductionQuestion => VerificationResult): VerificationResult = {
    abductionRules(rule).checkAndApply(q, rule)((q1, r1) => {
      if (r1 == abductionRules.length) {
        Q(q1)
      } else {
        applyRule(q1, r1)(Q)
      }
    })
  }
}

case class SiliconAbductionQuestion(s: State, v: Verifier, goal: Seq[Exp], foundPrecons: Seq[Exp] = Seq(), foundStmts: Seq[Stmt] = Seq()) extends AbductionQuestion {

  // TODO This should not live here, but in abstractions or abductions
  // Also this is super inefficient
  // Also there are cases where we have to transform not to inputs, but to other variables

  // TODO the original work introduces logical vars representing the original input values. They attempt (I think) to transform
  // to these vars. See the "Rename" algorithm in the original paper.
  // At the end, they can be re-replaced by the input parameters. Do we have to do this?
  def transformToInputs(e: Exp): Option[Exp] = {
    val inputs: Map[Term, LocalVar] = s.currentMember match {
      case Some(m: Method) => m.formalArgs.view.map(argDec => s.g.get(argDec.localVar).get -> argDec.localVar).toMap
      case _ => Map()
    }

    // Find the Vars in the Store which point to the same symbolic value as each input
    val aliases = inputs.keys.flatMap { t: Term => getVars(t, s.g).map(_ -> inputs(t)) }.toMap
    //s.g.values.collect({ case (v: LocalVar, t: Term) if inputs.contains(t) && !inputs.values.toSeq.contains(v) => v -> inputs(t) })

    // Find field chunks where the something points to an input var
    val pointers = s.h.values.collect { case c: BasicChunk if c.resourceID == FieldID && inputs.contains(c.snap) =>
      getVars(c.args.head, s.g).map(FieldAccess(_, getField(c.id))() -> inputs(c.snap))
    }.flatten.toMap

    //&& c.args.head.isInstanceOf[Var] => c.args.head -> inputs(c.snap)  }

    e match {
      case lc: LocalVar => aliases.get(lc)

      case Not(e1) => transformToInputs(e1).map(Not(_)())

      case And(e1, e2) =>
        val tra1 = transformToInputs(e1)
        val tra2 = transformToInputs(e2)
        if (tra1.isEmpty || tra2.isEmpty) None else Some(And(tra1.get, tra2.get)())

      case NeCmp(e1, e2) =>
        val tra1 = transformToInputs(e1)
        val tra2 = transformToInputs(e2)
        if (tra1.isEmpty || tra2.isEmpty) None else Some(NeCmp(tra1.get, tra2.get)())


      case EqCmp(e1, e2) =>
        val tra1 = transformToInputs(e1)
        val tra2 = transformToInputs(e2)
        if (tra1.isEmpty || tra2.isEmpty) None else Some(EqCmp(tra1.get, tra2.get)())


      case nl: NullLit => Some(nl)

      case fa: FieldAccess =>
        if(pointers.contains(fa)){
          Some(pointers(fa))
        } else {
          transformToInputs(fa.rcv).map{rcv1: Exp => fa.copy(rcv = rcv1)(fa.pos, fa.info, fa.errT)}
        }

      case fap: FieldAccessPredicate => transformToInputs(fap.loc).collect{case e1: FieldAccess => fap.copy(loc = e1)(fap.pos, fap.info, fap.errT)}

      case pa: PredicateAccess => val traArgs =pa.args.map(transformToInputs)
        if(traArgs.contains(None)) None else Some(pa.copy(args = traArgs.map(_.get))(pa.pos, pa.info, pa.errT))

      case pap: PredicateAccessPredicate => transformToInputs(pap.loc).collect{case e1: PredicateAccess => pap.copy(loc = e1)(pap.pos, pap.info, pap.errT) }

      case MagicWand(e1, e2) => val tra1 = transformToInputs(e1)
        val tra2 = transformToInputs(e2)
        if (tra1.isEmpty || tra2.isEmpty) None else Some(MagicWand(tra1.get, tra2.get)())

    }
  }

  private def getVars(t: Term, g: Store): Seq[AbstractLocalVar] = {
    g.values.collect({ case (v, t1) if t1 == t => v }).toSeq
  }

  private def getField(name: BasicChunkIdentifier) = {
    s.program.fields.find(_.name == name.name).get
  }
}

trait BiAbductionRule[T] {

  val pve: PartialVerificationError = Internal()

  def checkAndApply(q: SiliconAbductionQuestion, rule: Int)(Q: (SiliconAbductionQuestion, Int) => VerificationResult): VerificationResult = {
    check(q) {
      case Some(e) => apply(q, e)(Q(_, 0))
      case None => Q(q, rule + 1)
    }
  }

  protected def check(q: SiliconAbductionQuestion)(Q: Option[T] => VerificationResult): VerificationResult

  protected def apply(q: SiliconAbductionQuestion, inst: T)(Q: SiliconAbductionQuestion => VerificationResult): VerificationResult

  // TODO We currently assume that there is only one predicate and one field
  protected def getPredicate(q: SiliconAbductionQuestion, rec: Exp, p: Exp): PredicateAccessPredicate = {
    PredicateAccessPredicate(PredicateAccess(Seq(rec), q.s.program.predicates.head.name)(), p)()
  }

  protected def getNextAccess(q: SiliconAbductionQuestion, rec: Exp, p: Exp): FieldAccessPredicate = {
    FieldAccessPredicate(FieldAccess(rec, q.s.program.fields.head)(), p)()
  }
}

