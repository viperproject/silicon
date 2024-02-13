package viper.silicon.biabduction

import viper.silicon.interfaces.{Failure, VerificationResult}
import viper.silicon.resources.FieldID
import viper.silicon.state.{BasicChunk, BasicChunkIdentifier, State, Store}
import viper.silicon.state.terms.Term
import viper.silicon.utils.ast.BigAnd
import viper.silver.ast._
import viper.silver.verifier.errors.Internal
import viper.silver.verifier.{DummyReason, PartialVerificationError}

object BiAbductionSolver {


  def solve(q: SiliconAbductionQuestion): String = {

    val q1 = AbductionApplier.apply(q)

    if (q1.goal.isEmpty) {

      val varTrans = varTransformer(q1.s)

      // TODO it is possible that we want to transform variable in a non-strict way before abstraction
      val pres = AbstractionApplier.apply(AbstractionQuestion(q1.foundPrecons, q1.s)).exps


      // TODO if some path conditions already contain Ands, then we might reject clauses that we could actually handle
      val bcs = BigAnd(q1.v.decider.pcs.branchConditionExps.collect { case Some(e) if varTrans.transformToInputs(e).isDefined => varTrans.transformToInputs(e).get })

      val rt = pres.map { (e: Exp) =>
        (varTrans.transformToInputs(e), bcs) match {
          case (Some(e1), TrueLit()) => e1.toString()
          case (Some(e1), bcs) => Implies(bcs, e1)().toString()
          case _ => "Could not be transformed to inputs: " + e.toString()
        }
      }.mkString("\n")
      "Abduction successful.\nAbduced preconditions:\n" + rt + "\nAbduced statements:\n" + q1.foundStmts.map(_.toString()).mkString("\n")
    } else {
      "Abduction failed."
    }
  }
}

trait RuleApplier[S] {

  val rules: Seq[BiAbductionRule[S, _]]

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

  def checkAndApply(q: S, rule: Int)(Q: (S, Int) => VerificationResult): VerificationResult = {
    check(q) {
      case Some(e) => apply(q, e)(Q(_, 0))
      case None => Q(q, rule + 1)
    }
  }

  protected def check(q: S)(Q: Option[T] => VerificationResult): VerificationResult

  protected def apply(q: S, inst: T)(Q: S => VerificationResult): VerificationResult

  // TODO We currently assume that there is only one predicate and one field
  protected def getPredicate(p: Program, rec: Exp, e: Exp): PredicateAccessPredicate = {
    PredicateAccessPredicate(PredicateAccess(Seq(rec), p.predicates.head.name)(), e)()
  }

  protected def getNextAccess(p: Program, rec: Exp, e: Exp): FieldAccessPredicate = {
    FieldAccessPredicate(FieldAccess(rec, p.fields.head)(), e)()
  }
}

case class varTransformer(s: State) {

  private def getVars(t: Term, g: Store): Seq[AbstractLocalVar] = {
    g.values.collect({ case (v, t1) if t1 == t => v }).toSeq
  }

  private def getField(name: BasicChunkIdentifier) = {
    s.program.fields.find(_.name == name.name).get
  }

  // TODO
  // This is super inefficient
  // There are cases where we have to transform not to inputs, but to other variables
  // We also want a non-strict transformation, which does not fail

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
}

