package semper
package silicon
package ast

import annotation.tailrec

object expressions {
  @tailrec
  def getInnermostExpr(e: ast.Expression): ast.Expression = e match {
    case gop: ast.GhostOperation => getInnermostExpr(gop.body)
    case _ => e // TODO: Check that e doesn't contain further ghost operations
  }
}
