package viper.silicon.biabduction

import viper.silicon.interfaces.{Failure, VerificationResult}
import viper.silicon.resources.{FieldID, PredicateID}
import viper.silicon.state.terms.Term
import viper.silicon.state._
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
      val bcs = BigAnd(q1.v.decider.pcs.branchConditionExps.collect { case Some(e) if varTrans.transformExp(e).isDefined => varTrans.transformExp(e).get })

      // TODO Weak transformation of statements to original variables

      val rt = pres.map { (e: Exp) =>
        (varTrans.transformExp(e), bcs) match {
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

object abductionUtils {
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

case class varTransformer(s: State, targets: Seq[LocalVar], strict: Boolean = true) {

  // A map of symbolic term to the local var in the target set
  val targetMap: Map[Term, LocalVar] = targets.view.map(localVar => s.g.get(localVar).get -> localVar).toMap

  // Field Chunks where the snap is equal to the symbolic value of a target
  val snaps: Seq[BasicChunk] = s.h.values.collect { case c: BasicChunk if c.resourceID == FieldID && targetMap.contains(c.snap) => c }.toSeq

  // Chunks where the args are equal to the symbolic value of a target
  val args: Seq[BasicChunk] = s.h.values.collect { case c: BasicChunk if targetMap.contains(c.args.head) => c }.toSeq

  // We should look at the path conditions of a verifier as well

  def transformChunk(b: BasicChunk): Option[Exp] = {

    val rcv = transformTerm(b.args.head)
    (b, rcv) match {
      case (_, None) => None
      case (BasicChunk(FieldID, _, _, _, _), rcv) => Some(FieldAccessPredicate(FieldAccess(rcv.get, abductionUtils.getField(b.id, s.program))(), transformTerm(b.perm).get)())
      case (BasicChunk(PredicateID, _, _, _, _), rcv) => Some(abductionUtils.getPredicate(s.program, rcv.get, transformTerm(b.perm).get))
    }
  }

  def transformTerm(t: Term): Option[Exp] = {

    t match {
      case terms.FullPerm => Some(FullPerm()())
      case terms.Var(_, _) =>

        // Check for direct aliases
        val direct = targetMap.get(t)
        if (direct.isDefined) {
          return direct
        }

        // Check for field accesses pointing to the term
        val parents = s.h.values.collect { case c: BasicChunk if c.resourceID == FieldID && c.snap == t => c }
        val matches = parents.map { c => c -> transformTerm(c.args.head) }.collect { case (c, Some(e)) => c -> e }
        if (matches.nonEmpty) {
          val res = matches.head
          return Some(FieldAccess(res._2, abductionUtils.getField(res._1.id, s.program))())
        }
        // TODO we should check the path conditions for equalities that allow us to search further
        None

      }
    }

  // TODO the original work introduces logical vars representing the original input values. They attempt (I think) to transform
  // to these vars. See the "Rename" algorithm in the original paper.
  // At the end, they can be re-replaced by the input parameters. Do we have to do this?
  def transformExp(e: Exp): Option[Exp] = {

    // Get direct aliases by matching each target var to other vars that have the same symbolic term
    // If x is the target, this will find x = y
    val aliases = targetMap.keys.flatMap { t: Term => abductionUtils.getVars(t, s.g).map(_ -> targetMap(t)) }.toMap

    // Field accesses where the snapshot is equal to the symbolic value of a target
    // If x is the target, this will find y.next = x
    val pointers = snaps.flatMap { c =>
      abductionUtils.getVars(c.args.head, s.g).map(FieldAccess(_, abductionUtils.getField(c.id, s.program))() -> targetMap(c.snap))
    }.toMap

    e match {
      case lc: LocalVar =>
        val lcTra = aliases.get(lc)
        if (lcTra.isEmpty && !strict) Some(lc) else lcTra

      case Not(e1) => transformExp(e1).map(Not(_)())

      case And(e1, e2) =>
        val tra1 = transformExp(e1)
        val tra2 = transformExp(e2)
        if (tra1.isEmpty || tra2.isEmpty) None else Some(And(tra1.get, tra2.get)())

      case NeCmp(e1, e2) =>
        val tra1 = transformExp(e1)
        val tra2 = transformExp(e2)
        if (tra1.isEmpty || tra2.isEmpty) None else Some(NeCmp(tra1.get, tra2.get)())


      case EqCmp(e1, e2) =>
        val tra1 = transformExp(e1)
        val tra2 = transformExp(e2)
        if (tra1.isEmpty || tra2.isEmpty) None else Some(EqCmp(tra1.get, tra2.get)())


      case nl: NullLit => Some(nl)

      case fa: FieldAccess =>
        if (pointers.contains(fa)) {
          Some(pointers(fa))
        } else {
          transformExp(fa.rcv).map { rcv1: Exp => fa.copy(rcv = rcv1)(fa.pos, fa.info, fa.errT) }
        }

      case fap: FieldAccessPredicate => transformExp(fap.loc).collect { case e1: FieldAccess => fap.copy(loc = e1)(fap.pos, fap.info, fap.errT) }

      case pa: PredicateAccess => val traArgs = pa.args.map(transformExp)
        if (traArgs.contains(None)) None else Some(pa.copy(args = traArgs.map(_.get))(pa.pos, pa.info, pa.errT))

      case pap: PredicateAccessPredicate => transformExp(pap.loc).collect { case e1: PredicateAccess => pap.copy(loc = e1)(pap.pos, pap.info, pap.errT) }

      case MagicWand(e1, e2) => val tra1 = transformExp(e1)
        val tra2 = transformExp(e2)
        if (tra1.isEmpty || tra2.isEmpty) None else Some(MagicWand(tra1.get, tra2.get)())
    }
  }
}

