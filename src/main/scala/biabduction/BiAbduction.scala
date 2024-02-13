package viper.silicon.biabduction

import viper.silicon.interfaces.{Failure, VerificationResult}
import viper.silicon.resources.FieldID
import viper.silicon.state.{BasicChunk, BasicChunkIdentifier, State, Store}
import viper.silicon.state.terms.Term
import viper.silicon.utils.ast.BigAnd
import viper.silver.ast._
import viper.silver.verifier.errors.Internal
import viper.silver.verifier.{DummyReason, PartialVerificationError}

// TODO we want to continue execution if we abduce successfully. Idea:
// - Hook into the "Try or Fail" methods
// - Instead of actually failing, do bi-abduction
// - track the results somewhere
// - produce the precondition, execute the statements, and continue execution
// - At the end, do abstraction on all the found preconditions. Find the necessary statements for the abstractions

object BiAbductionSolver {

  def solve(q: SiliconAbductionQuestion): String = {

    val q1 = AbductionApplier.apply(q)

    if (q1.goal.isEmpty) {

      val ins = q1.s.currentMember match {
        case Some(m: Method) => m.formalArgs.map(_.localVar)
        case _ => Seq()
      }
      val varTrans = varTransformer(q1.s, ins)

      // TODO it is possible that we want to transform variable in a non-strict way before abstraction
      val pres = AbstractionApplier.apply(AbstractionQuestion(q1.foundPrecons, q1.s)).exps

      // TODO if some path conditions already contain Ands, then we might reject clauses that we could actually handle
      val bcs = BigAnd(q1.v.decider.pcs.branchConditionExps.collect { case Some(e) if varTrans.transformVars(e).isDefined => varTrans.transformVars(e).get })

      // TODO Weak transformation of statements to original variables

      val rt = pres.map { (e: Exp) =>
        (varTrans.transformVars(e), bcs) match {
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

object utils {
  // TODO We currently assume that there is only one predicate and one field
  def getPredicate(p: Program, rec: Exp, e: Exp): PredicateAccessPredicate = {
    PredicateAccessPredicate(PredicateAccess(Seq(rec), p.predicates.head.name)(), e)()
  }

  def getNextAccess(p: Program, rec: Exp, perm: Exp): FieldAccessPredicate = {
    FieldAccessPredicate(FieldAccess(rec, p.fields.head)(), perm)()
  }

  def getVars(t: Term, g: Store): Seq[AbstractLocalVar] = {
    g.values.collect({ case (v, t1) if t1 == t => v }).toSeq
  }

  def getField(name: BasicChunkIdentifier, p: Program) = {
    p.fields.find(_.name == name.name).get
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

}

case class varTransformer(s: State, targets: Seq[LocalVar], strict: Boolean = true) {

  // TODO the original work introduces logical vars representing the original input values. They attempt (I think) to transform
  // to these vars. See the "Rename" algorithm in the original paper.
  // At the end, they can be re-replaced by the input parameters. Do we have to do this?
  def transformVars(e: Exp): Option[Exp] = {

    val targetMap: Map[Term, LocalVar] = targets.view.map(localVar => s.g.get(localVar).get -> localVar).toMap

    // Find the Vars in the Store which point to the same symbolic value as each input
    val aliases = targetMap.keys.flatMap { t: Term => utils.getVars(t, s.g).map(_ -> targetMap(t)) }.toMap
    //s.g.values.collect({ case (v: LocalVar, t: Term) if inputs.contains(t) && !inputs.values.toSeq.contains(v) => v -> inputs(t) })

    // Find field chunks where the something points to an input var
    val pointers = s.h.values.collect { case c: BasicChunk if c.resourceID == FieldID && targetMap.contains(c.snap) =>
      utils.getVars(c.args.head, s.g).map(FieldAccess(_, utils.getField(c.id, s.program))() -> targetMap(c.snap))
    }.flatten.toMap

    e match {
      case lc: LocalVar =>
        val lcTra = aliases.get(lc)
        if (lcTra.isEmpty && !strict) Some(lc) else lcTra

      case Not(e1) => transformVars(e1).map(Not(_)())

      case And(e1, e2) =>
        val tra1 = transformVars(e1)
        val tra2 = transformVars(e2)
        if (tra1.isEmpty || tra2.isEmpty) None else Some(And(tra1.get, tra2.get)())

      case NeCmp(e1, e2) =>
        val tra1 = transformVars(e1)
        val tra2 = transformVars(e2)
        if (tra1.isEmpty || tra2.isEmpty) None else Some(NeCmp(tra1.get, tra2.get)())


      case EqCmp(e1, e2) =>
        val tra1 = transformVars(e1)
        val tra2 = transformVars(e2)
        if (tra1.isEmpty || tra2.isEmpty) None else Some(EqCmp(tra1.get, tra2.get)())


      case nl: NullLit => Some(nl)

      case fa: FieldAccess =>
        if (pointers.contains(fa)) {
          Some(pointers(fa))
        } else {
          transformVars(fa.rcv).map { rcv1: Exp => fa.copy(rcv = rcv1)(fa.pos, fa.info, fa.errT) }
        }

      case fap: FieldAccessPredicate => transformVars(fap.loc).collect { case e1: FieldAccess => fap.copy(loc = e1)(fap.pos, fap.info, fap.errT) }

      case pa: PredicateAccess => val traArgs = pa.args.map(transformVars)
        if (traArgs.contains(None)) None else Some(pa.copy(args = traArgs.map(_.get))(pa.pos, pa.info, pa.errT))

      case pap: PredicateAccessPredicate => transformVars(pap.loc).collect { case e1: PredicateAccess => pap.copy(loc = e1)(pap.pos, pap.info, pap.errT) }

      case MagicWand(e1, e2) => val tra1 = transformVars(e1)
        val tra2 = transformVars(e2)
        if (tra1.isEmpty || tra2.isEmpty) None else Some(MagicWand(tra1.get, tra2.get)())
    }
  }
}

