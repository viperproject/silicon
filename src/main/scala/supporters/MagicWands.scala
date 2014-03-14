package semper
package silicon
package supporters

import scala.collection.mutable.ListBuffer
import interfaces.state.{State, PathConditions, Heap, Store}
import interfaces.reporting.Context
import state.{MagicWandChunk, terms}

class MagicWandSupporter[ST <: Store[ST],
                         H <: Heap[H],
                         PC <: PathConditions[PC],
                         S <: State[ST, H, S],
                         C <: Context[C, ST, H, S]] {

  def resolveWand(σ: S, exp: ast.Expression): (ast.MagicWand, Map[ast.LocalVariable, terms.Term]) = exp match {
    case wand: ast.MagicWand =>
      (wand, Map())

    case v: ast.LocalVariable =>
      val ch = σ.γ(v).asInstanceOf[terms.WandChunkRef[H]].ch

      /* Give all local vars fresh names. This ensures that we can add them to
       * a store without risking to overwrite existing local variables.
       * Renaming is currently necessary because local variables inside wands
       * in wand chunks are always given the same names when the wand chunk
       * is created. (Having unique local variable names makes it easy to compare
       * wands for syntactic equality modulo variable names.)
       *
       * TODO: [Malte] Renaming is - I think - only necessary for local variables
       *       inside pold-expressions (see consume/wand).
       *       It might be simpler to evaluate those
       *       when creating the wand chunk, and to replace the expressions by
       *       fresh variables $pold_i which can be mapped to the value the
       *       replaced pold-expressions had.
       */
      val lvs = ch.localVariables map (lv => silicon.ast.utils.fresh(lv))

      /* Create mappings from these fresh variables to the receivers that come with the chunk */
      val map: Map[ast.LocalVariable, terms.Term] = toMap(lvs zip ch.localVariableValues)
      val wand = sil.ast.utility.Expressions.instantiateVariables(ch.renamedWand, ch.localVariables, lvs)

      (wand, map)

    case _ => sys.error(s"Unexpected expression $exp (${exp.getClass.getName}})")
  }

  def pathConditionedPOlds(wand: ast.MagicWand): Seq[(ast.Expression, ast.PackageOld)] = {
    val polds = new ListBuffer[(ast.Expression, ast.PackageOld)]()
    val cs = Seq[ast.Expression]()

    pathConditionedPOlds(wand.left, cs, polds)
    pathConditionedPOlds(wand.right, cs, polds)

    polds.toList
  }

  private def pathConditionedPOlds(e: ast.Expression, conditions: Seq[ast.Expression], polds: ListBuffer[(ast.Expression, ast.PackageOld)]) {
    e.visitWithContextManually(conditions)(cs => {
      case ast.Implies(e0, e1) =>
        pathConditionedPOlds(e0, conditions, polds)
        pathConditionedPOlds(e1, conditions ++ Seq(e0), polds)

      case ast.Ite(e0, e1, e2) =>
        pathConditionedPOlds(e0, conditions, polds)
        pathConditionedPOlds(e1, conditions ++ Seq(e0), polds)
        pathConditionedPOlds(e2, conditions ++ Seq(ast.Not(e0)(e0.pos, e0.info)), polds)

      case po: ast.PackageOld =>
        polds += ((ast.utils.BigAnd(conditions), po))
   })
  }

  /* TODO: Can we separate it into evaluating a chunk into a ChunkTerm and constructing a chunk carrying
   *       that term?
   */
  def createChunk(γ: ST, hPO: H, wand: ast.MagicWand) = {
    /* Remove all ghost operations and keep only the real rhs of the wand */
    val ghostFreeWand = wand.copy(right = ast.expressions.getInnermostExpr(wand.right))(wand.pos, wand.info)

    var vs = new ListBuffer[ast.LocalVariable]()
    var ts = new ListBuffer[terms.Term]()
    var i = 0

    /* Collect all local variables and their values.
     * Rename local variables to $lv_i to simplify comparing wands syntactically,
     * which is currently done to find a potentially matching wand chunk in the
     * heap when consuming a wand.
     */
    val renamedWand = ghostFreeWand.transform {
      case lv: ast.LocalVariable =>
        val id = "$lv" + i
        val v = ast.LocalVariable(id)(lv.typ, lv.pos, lv.info)

        vs += v
        ts += γ(lv)
        i += 1

        v
    }()

    /* Keeping the list of local variables is not necessary, it could be computed
     * from ghostFreeWand when needed.
     */
    MagicWandChunk(ghostFreeWand, renamedWand, vs, ts, hPO)
  }
}
