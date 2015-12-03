/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon

import interfaces.state.{Store, Heap, State, StateFormatter}
import state.terms._

class DefaultStateFormatter[ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]]
                           (val config: Config)
    extends StateFormatter[ST, H, S, String] {

  def format(σ: S) = {
    val γ = format(σ.γ)
    val h = format(σ.h, "h")
    val g = format(σ.g, "g")

    val π =
      if (config.logLevel().equalsIgnoreCase("TRACE") || config.logLevel().equalsIgnoreCase("ALL"))
        s"  ${format(σ.π)}\n"
      else
        ""

    s"""σ(
       |  $γ,
       |  $h,
       |  $g,
       |  $π)""".stripMargin
  }

  def format(γ: ST) = {
    val map = γ.values
    if (map.isEmpty) "Ø" else "γ" + map.mkString("(", ", ", ")")
  }

  def format(h: H) = format(h, "h")

  private def format(h: H, id: String) = {
    val values = h.values
    if (values.isEmpty) "Ø" else id + values.mkString("(", ", ", ")")
  }

  def format(π: Set[Term]) = {
    /* Attention: Hides non-null and combine terms. */
    if (π.isEmpty) "Ø"
    else
      "π" + π.filterNot {
        case c: BuiltinEquals if    c.p0.isInstanceOf[Combine]
                || c.p1.isInstanceOf[Combine] => true
        case Not(BuiltinEquals(_, Null())) => true
        case _ => false
      }.mkString("(", ", ", ")")
  }
}
