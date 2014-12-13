/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon
package ast

//import silver.utility.SilNameGenerator
import silicon.utils.mapReduceLeft

package object utils {
  def BigAnd(it: Iterable[ast.Expression],
             f: ast.Expression => ast.Expression = e => e,
             emptyPos: SourcePosition = ast.NoPosition) =

    mapReduceLeft(it,
                  f,
                  (e0: ast.Expression, e1: ast.Expression) => ast.And(e0, e1)(e0.pos, e0.info),
                  ast.True()(emptyPos))

//  val nameGenerator = new SilNameGenerator()

  def fresh(name: String,
            typ: ast.Type,
            pos: silver.ast.Position = NoPosition,
            info: silver.ast.Info = silver.ast.NoInfo) =

    ast.LocalVariable(s"$name$$$$${counter.next()}")(typ, pos, info)

  def fresh(lv: ast.Variable) =
    ast.LocalVariable(s"${lv.name}$$$$${counter.next()}")(lv.typ, lv.pos, lv.info)

  private object counter {
    private var value = 0

    def next() = {
      value = value + 1
      value
    }

    def reset() {
      value = 0
    }
  }
}
