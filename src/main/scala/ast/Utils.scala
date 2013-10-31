package semper
package silicon
package ast

import sil.utility.SilNameGenerator
import silicon.utils.mapReduceLeft

package object utils {
  def BigAnd(it: Iterable[ast.Expression],
             f: ast.Expression => ast.Expression = e => e,
             emptyPos: SourcePosition = ast.NoPosition) =

    mapReduceLeft(it,
                  f,
                  (e0: ast.Expression, e1: ast.Expression) => ast.And(e0, e1)(e0.pos, e0.info),
                  ast.True()(emptyPos))

  val nameGenerator = new SilNameGenerator()

  /* TODO: Does Sil already provide this functionality? If not, move it into Sil. Same for BigAnd? */
  def fresh(name: String, typ: ast.Type, pos: sil.ast.Position = NoPosition, info: sil.ast.Info = sil.ast.NoInfo) =
    ast.LocalVariable(nameGenerator.createIdentifier(name))(typ, pos, info)

  def fresh(lv: ast.Variable) =
    ast.LocalVariable(nameGenerator.createIdentifier(lv.name))(lv.typ, lv.pos, lv.info)
}
