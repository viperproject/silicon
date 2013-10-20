package semper
package silicon
package ast

import annotation.tailrec

object expressions {
  @tailrec
  def getInnermostExpr(e: ast.Expression): ast.Expression = e match {
    case ast.Folding(_, eIn) => getInnermostExpr(eIn)
    case ast.Applying(_, eIn) => getInnermostExpr(eIn)
    case _ => e // TODO: Check that e doesn't contain further ghost operations
  }
}
