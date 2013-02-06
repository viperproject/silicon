package semper
package silicon
package ast.utils

import silicon.utils.collections.mapReduceLeft

object collections {
  private def createSILAnd(ef: ast.ExpressionFactory)(e0: ast.Expression, e1: ast.Expression) = {
    val loc = e0.sourceLocation
    ef.makeBinaryExpression(ast.And()(loc), e0, e1, loc, Nil)
  }

  def BigAnd(ef: ast.ExpressionFactory)(it: Iterable[ast.Expression], f: ast.Expression => ast.Expression = e => e) =
    mapReduceLeft(it, f, createSILAnd(ef), ast.True()(ast.NoLocation))
}