package semper
package silicon
package ast

import silicon.utils.collections.mapReduceLeft

package object utils {
//  private def createSILAnd(ef: ast.ExpressionFactory)(e0: ast.Expression, e1: ast.Expression) = {
//    val loc = e0.sourceLocation
//    ef.makeBinaryExpression(ast.And()(loc), e0, e1, loc, Nil)
//  }

  def BigAnd(it: Iterable[ast.Expression], f: ast.Expression => ast.Expression = e => e) =
    mapReduceLeft(it,
                  f,
                  (e0: ast.Expression, e1: ast.Expression) => ast.And(e0, e1)(e0.pos, e0.info),
                  ast.True()(ast.NoPosition))
}