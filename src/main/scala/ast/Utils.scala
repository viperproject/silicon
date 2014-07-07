/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package semper
package silicon
package ast

import silicon.utils.mapReduceLeft

package object utils {
  def BigAnd(it: Iterable[ast.Expression],
             f: ast.Expression => ast.Expression = e => e,
             emptyPos: SourcePosition = ast.NoPosition) =

    mapReduceLeft(it,
                  f,
                  (e0: ast.Expression, e1: ast.Expression) => ast.And(e0, e1)(e0.pos, e0.info),
                  ast.True()(emptyPos))
}
