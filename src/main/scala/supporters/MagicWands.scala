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
      // give all local vars fresh names
      val lvs = ch.localVariables map (lv => silicon.ast.utils.fresh(lv))
      val wand = sil.ast.utility.Expressions.instantiateVariables(ch.wandInstance, ch.localVariables, lvs)
      // create mappings from these fresh variables to the receivers that come with the chunk
      val map: Map[ast.LocalVariable, terms.Term] = (lvs zip ch.localVariableValues).toMap
      // return fresh chunk AST and mappings
      (wand, map)

    case _ => sys.error(s"Unexpected expression $exp (${exp.getClass.getName}})")
  }

  /* TODO: Move into another file, shouldn't be part of the Producer. MagicWandSupport? ChunksUtils?
   *       Can we separate it into evaluating a chunk into a ChunkTerm and constructing a chunk carrying
   *       that term?
   */
  def createChunk(γ: ST, hPO: H, wand: ast.MagicWand) = {
    val essentialWand = wand.copy(right = ast.expressions.getInnermostExpr(wand.right))(wand.pos, wand.info)

    var vs = new ListBuffer[ast.LocalVariable]()
    var ts = new ListBuffer[terms.Term]()
    var i = 0

    val instantiatedWand = essentialWand.transform {
      case lv: ast.LocalVariable =>
        val id = "$lv" + i
        val v = ast.LocalVariable(id)(lv.typ, lv.pos, lv.info)

        vs += v
        ts += γ(lv)
        i += 1

        v
    }()

    MagicWandChunk(instantiatedWand, vs, ts, hPO)
  }
}
