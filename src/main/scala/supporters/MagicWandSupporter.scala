package viper
package silicon
package supporters

import com.weiglewilczek.slf4s.Logging
import silver.verifier.PartialVerificationError
import silver.verifier.reasons.InsufficientPermission
import interfaces.{Evaluator, VerificationResult, Failure}
import interfaces.decider.Decider
import interfaces.state.{ChunkIdentifier, State, PathConditions, Heap, Store}
import viper.silicon.state.{DefaultContext, DirectChunk, DirectPredicateChunk, DirectFieldChunk, MagicWandChunk}
import state.terms._
import state.terms.perms.{IsNoAccess, IsAsPermissive}

trait MagicWandSupporter[ST <: Store[ST],
                         H <: Heap[H],
                         PC <: PathConditions[PC],
                         S <: State[ST, H, S]]
    { this:      Logging
            with Evaluator[ST, H, S, DefaultContext[H]] =>

//class MagicWandSupporter[ST <: Store[ST],
//                         H <: Heap[H],
//                         PC <: PathConditions[PC],
//                         S <: State[ST, H, S],
//                         C <: Context[C]]
//                        (decider: Decider[DefaultFractionalPermissions, ST, H, PC, S, C]) {

  protected val decider: Decider[ST, H, PC, S, DefaultContext[H]]

  object magicWandSupporter {

  private type C = DefaultContext[H]

  def isDirectWand(exp: ast.Expression) = exp match {
    case wand: ast.MagicWand => true
    case v: ast.LocalVariable => v.typ == ast.types.Wand
    case _ => false
  }

//  def translate(σ: S, eWand: ast.MagicWand, pve: PartialVerificationError, c: C)
//               (Q: (Term, C) => VerificationResult)
//               : VerificationResult = {
//
//    decider.locally[(shapes.MagicWand, C)](QL =>
//      translate(σ, eWand.left, pve, c)((tLeft, c1) =>
//        translate(σ, eWand.right, pve, c1)((tRight, c2) =>
//          QL(shapes.MagicWand(tLeft, tRight), c2)))
//    ){case (tWand, c1) => Q(tWand, c1)}
//  }
//
//  protected def translate(σ: S, e: ast.Expression, pve: PartialVerificationError, c: C)
//                         (Q: (Term, C) => VerificationResult)
//                         : VerificationResult =
//
//    e match {
//      case ast.FieldAccessPredicate(ast.FieldAccess(eRcvr, field), ePerms) =>
//        eval(σ, eRcvr, pve, c)((tRcvr, c1) => {
//          decider.assume(tRcvr !== Null())
//          evalp(σ, ePerms, pve, c1)((tPerms, c2) =>
//            Q(shapes.Acc(PlainSymbol(field.name), tRcvr :: Nil, tPerms), c2))})
//
//      case ast.PredicateAccessPredicate(ast.PredicateAccess(eArgs, predicateName), ePerms) =>
//        evals(σ, eArgs, pve, c)((ts, c1) =>
//          evalp(σ, ePerms, pve, c1)((tPerms, c2) =>
//            Q(shapes.Acc(PlainSymbol(predicateName), ts, tPerms), c2)))
//
//      case and: ast.And if !and.isPure =>
//        translate(σ, and.left, pve, c)((tLeft, c1) =>
//          translate(σ, and.right, pve, c1)((tRight, c2) =>
//            Q(shapes.And(tLeft, tRight), c2)))
//
//      case ast.Implies(e0, e1) if !e.isPure =>
//        translate(σ, e0, pve, c)((t0, c1) =>
//          translate(σ, e1, pve, c1)((t1, c2) =>
//            Q(shapes.Implies(t0, t1), c2)))
//
//      case ast.Ite(e0, e1, e2) if !e.isPure =>
//        translate(σ, e0, pve, c)((t0, c1) =>
//          translate(σ, e1, pve, c1)((t1, c2) =>
//            translate(σ, e2, pve, c2)((t2, c3) =>
//              Q(shapes.Ite(t0, t1, t2), c3))))
//
//      case ast.MagicWand(e0, e1) =>
//        assert(!e.isPure, "Found a pure magic wand ... surprise!")
//        translate(σ, e0, pve, c)((t0, c1) =>
//          translate(σ, e1, pve, c1)((t1, c2) =>
//            Q(shapes.MagicWand(t0, t1), c2)))
//
//      case _ if e.isPure =>
//        eval(σ, e, pve, c)(Q)
//
//      case _ => sys.error(s"Assertion $e not yet supported")
//    }

//  def resolveWand(σ: S, exp: ast.Expression): (ast.MagicWand, Map[ast.LocalVariable, Term]) = {
//    assert(isDirectWand(exp),
//             "Only direct wands (wand-typed variables w, A --* B) can be resolved."
//           + "Wands wrapped in ghost operations (applying w in (A --* B)) cannot.")
//
//    exp match {
//      case wand: ast.MagicWand =>
//        (wand, Map())
//
//      case v: ast.LocalVariable =>
//        σ.γ(v).asInstanceOf[MagicWand]
//
////        val ch = σ.γ(v).asInstanceOf[MagicWand]
////
////        /* Give all local vars fresh names. This ensures that we can add them to
////       * a store without risking to overwrite existing local variables.
////       * Renaming is currently necessary because local variables inside wands
////       * in wand chunks are always given the same names when the wand chunk
////       * is created. (Having unique local variable names makes it easy to compare
////       * wands for syntactic equality modulo variable names.)
////       *
////       * TODO: [Malte] Renaming is - I think - only necessary for local variables
////       *       inside pold-expressions (see consume/wand).
////       *       It might be simpler to evaluate those
////       *       when creating the wand chunk, and to replace the expressions by
////       *       fresh variables $pold_i which can be mapped to the value the
////       *       replaced pold-expressions had.
////       */
////        val lvs = ch.localVariables map (lv => silicon.ast.utils.fresh(lv))
////
////        /* Create mappings from these fresh variables to the receivers that come with the chunk */
////        val map: Map[ast.LocalVariable, Term] = toMap(lvs zip ch.localVariableValues)
////        val wand = silver.ast.utility.Expressions.instantiateVariables(ch.renamedWand, ch.localVariables, lvs)
////
////        (wand, map)
//
//      case _ => sys.error(s"Unexpected expression $exp (${exp.getClass.getName}})")
//    }
//  }

//  def pathConditionedPOlds(wand: ast.MagicWand): Seq[(ast.Expression, ast.PackageOld)] = {
//    val polds = new mutable.ListBuffer[(ast.Expression, ast.PackageOld)]()
//    val cs = Seq[ast.Expression]()
//
//    pathConditionedPOlds(wand.left, cs, polds)
//    pathConditionedPOlds(wand.right, cs, polds)
//
//    polds.toList
//  }
//
//  private def pathConditionedPOlds(e: ast.Expression,
//                                   conditions: Seq[ast.Expression],
//                                   polds: mutable.ListBuffer[(ast.Expression, ast.PackageOld)]) {
//
//    e.visitWithContextManually(conditions)(cs => {
//      case ast.Implies(e0, e1) =>
//        pathConditionedPOlds(e0, conditions, polds)
//        pathConditionedPOlds(e1, conditions ++ Seq(e0), polds)
//
//      case ast.Ite(e0, e1, e2) =>
//        pathConditionedPOlds(e0, conditions, polds)
//        pathConditionedPOlds(e1, conditions ++ Seq(e0), polds)
//        pathConditionedPOlds(e2, conditions ++ Seq(ast.Not(e0)(e0.pos, e0.info)), polds)
//
//      case po: ast.PackageOld =>
//        polds += ((ast.utils.BigAnd(conditions), po))
//   })
//  }

  def createChunk(σ: S, wand: ast.MagicWand, pve: PartialVerificationError, c: C)
                 (Q: (MagicWandChunk, C) => VerificationResult)
                 : VerificationResult = {

    val ghostFreeWand = wand.withoutGhostOperations
    val es = ghostFreeWand.subexpressionsToEvaluate(c.program)
//    println(s"es = $es")

    evals(σ, es, pve, c)((ts, c1) =>
      Q(MagicWandChunk(ghostFreeWand, ts), c1))

//    var vs = mutable.ListBuffer[ast.LocalVariable]()
//    var ts = mutable.ListBuffer[Term]()
//    var i = 0
//
//    /* Collect all local variables and their values.
//     * Rename local variables to $lv_i to simplify comparing wands syntactically,
//     * which is currently done to find a potentially matching wand chunk in the
//     * heap when consuming a wand.
//     */
//    val renamedWand = ghostFreeWand.transform {
//      case lv: ast.LocalVariable =>
//        val id = "$lv" + i
//        val v = ast.LocalVariable(id)(lv.typ, lv.pos, lv.info)
//
//        vs += v
//        ts += γ(lv)
//        i += 1
//
//        v
//    }()
//
//    /* Keeping the list of local variables is not necessary, it could be computed
//     * from ghostFreeWand when needed.
//     */
////    MagicWandChunk[H](ghostFreeWand, renamedWand, vs, ts/*, hPO*/)
  }

  /* TODO: doWithMultipleHeaps and consumeFromMultipleHeaps have a similar
   *       structure. Try to merge the two.
   */

  def doWithMultipleHeaps[R](hs: Stack[H],
                             c: C)
                            (action: (H, C) => (Option[R], H, C))
                            (Q: (Option[R], Stack[H], C) => VerificationResult)
                            : VerificationResult = {

    var result: Option[R] = None
    var heapsToVisit = hs
    var visitedHeaps: List[H] = Nil
    var cCurr = c

    while (heapsToVisit.nonEmpty && result.isEmpty) {
      val h = heapsToVisit.head
      heapsToVisit = heapsToVisit.tail

      val (result1, h1, c1) = action(h, cCurr)
      result = result1
      visitedHeaps = h1 :: visitedHeaps
      cCurr = c1
    }

    Q(result, visitedHeaps.reverse ++ heapsToVisit, cCurr)
  }

  def consumeFromMultipleHeaps(σ: S,
                               hs: Stack[H],
                               id: ChunkIdentifier,
                               pLoss: Term,
                               locacc: ast.LocationAccess,
                               pve: PartialVerificationError,
                               c: C)
//                              (Q: (Stack[H], List[(DirectChunk, Int)], C) => VerificationResult)
                              (Q: (Stack[H], List[DirectChunk], C) => VerificationResult)
                              : VerificationResult = {

    var toLose = pLoss
    var heapsToVisit = hs
    var visitedHeaps: List[H] = Nil
//    var chunks: List[(DirectChunk, Int)] = Nil
    var chunks: List[DirectChunk] = Nil
    var cCurr = c

//    println("\n[consumeFromMultipleHeaps]")
//    println(s"  toLose = $toLose")
//    println(s"  heapsToVisit = $heapsToVisit")
//    println(s"  visitedHeaps = $visitedHeaps")
//    println(s"  chunks = $chunks")

    while (heapsToVisit.nonEmpty && !decider.check(σ, IsNoAccess(toLose))) {
      val h = heapsToVisit.head
      heapsToVisit = heapsToVisit.tail

//      println(s"\n  h = $h")
      val (h1, optCh1, toLose1, c1) = consumeMaxPermissions(σ, h, id, toLose, cCurr)
//      println(s"  h1 = $h1")
//      println(s"  optCh1 = $optCh1")
//      println(s"  toLose1 = $toLose1")
      visitedHeaps = h1 :: visitedHeaps
      chunks =
        optCh1 match {
          case None => chunks
//          case Some(ch) => (ch, visitedHeaps.length  - 1) :: chunks
          case Some(ch) => ch :: chunks
        }
      toLose = toLose1
      cCurr = c1
    }

//    println(s"\n  X toLose = $toLose")
//    println(s"  X heapsToVisit = $heapsToVisit")
//    println(s"  X visitedHeaps = $visitedHeaps")
//    println(s"  X chunks = $chunks")

    if (decider.check(σ, IsNoAccess(toLose))) {
      val tEqs =
        chunks.sliding(2).map {
//          case List((fc1: DirectFieldChunk, _), (fc2: DirectFieldChunk, _)) => fc1.value === fc2.value
          case List(fc1: DirectFieldChunk, fc2: DirectFieldChunk) => fc1.value === fc2.value
//          case List((pc1: DirectPredicateChunk, _), (pc2: DirectPredicateChunk, _)) => pc1.snap === pc2.snap
          case List(pc1: DirectPredicateChunk, pc2: DirectPredicateChunk) => pc1.snap === pc2.snap
          case _ => True()
        }

      decider.assume(toSet(tEqs))

//      val pcr = PermissionsConsumptionResult(false) // TODO: PermissionsConsumptionResult is bogus!

      Q(visitedHeaps.reverse ++ heapsToVisit, chunks.reverse, cCurr/*, pcr*/)
    } else {
      Failure[ST, H, S](pve dueTo InsufficientPermission(locacc))
    }
  }

  /* TODO: This is similar, but not as general, as the consumption algorithm
   *       implemented for supporting quantified permissions. It should be
   *       possible to unite the two.
   */
  private def consumeMaxPermissions(σ: S,
                                    h: H,
                                    id: ChunkIdentifier,
                                    pLoss: Term,
                                    c: C)
                                   : (H, Option[DirectChunk], Term, C) = {

    decider.getChunk[DirectChunk](σ, h, id, c) match {
      case result @ Some(ch) =>
        val (pLost, pKeep, pToConsume) =
          if (decider.check(σ, IsAsPermissive(ch.perm, pLoss)))
            (pLoss, PermMinus(ch.perm, pLoss), NoPerm())
          else
            (ch.perm, NoPerm(), PermMinus(pLoss, ch.perm))
//        println("  [consumeMaxPermissions]")
//        println(s"    ch.perm = ${ch.perm}")
//        println(s"    pLost = $pLost")
//        println(s"    pKeep = $pKeep")
//        println(s"    pToConsume = $pToConsume")
        val h1 =
          if (decider.check(σ, IsNoAccess(pKeep))) h - ch
          else h - ch + (ch \ pKeep)
        val consumedChunk = ch \ pLost
        (h1, Some(consumedChunk), pToConsume, c)

      case None => (h, None, pLoss, c)
    }
  }
  }
}
