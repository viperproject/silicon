/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.reporting

import viper.silicon._
import viper.silicon.interfaces.state.{Heap, State, StateFormatter, Store}
import viper.silicon.state.terms._

class DefaultStateFormatter[ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]]
                           (val config: Config)
    extends StateFormatter[ST, H, S, String] {

  def format(σ: S, π: Set[Term]): String = {
    val γStr = format(σ.γ)
    val hStr = format(σ.h, "h")
    val gStr = format(σ.g, "g")

    val πStr =
      if (config.logLevel().equalsIgnoreCase("TRACE") || config.logLevel().equalsIgnoreCase("ALL"))
        s"${format(π)}\n"
      else
        ""

    s"""state(
       |  $γStr,
       |  $hStr,
       |  $gStr,
       |  $πStr)""".stripMargin
  }

  def format(γ: ST): String = {
    val map = γ.values
    if (map.isEmpty) "{}" else "store" + map.mkString("(", ", ", ")")
  }

  def format(h: H): String = format(h, "h")

  private def format(h: H, id: String): String = {
    val values = h.values
    if (values.isEmpty) "{}" else id + values.mkString("(", ", ", ")")
  }

  def format(π: Set[Term]): String = {
    /* Attention: Hides non-null and combine terms. */
    if (π.isEmpty) "{}"
    else
      "pcs" + π.filterNot {
        case c: BuiltinEquals if    c.p0.isInstanceOf[Combine]
                || c.p1.isInstanceOf[Combine] => true
        case Not(BuiltinEquals(_, Null())) => true
        case _ => false
      }.mkString("(", ", ", ")")
  }
}
