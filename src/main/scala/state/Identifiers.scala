/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.state

import viper.silver.components.StatefulComponent
import viper.silicon.utils.Counter

sealed trait Identifier {
  def name: String
  def rename(fn: String => String): Identifier

  def withSuffix(suffix: String): SuffixedIdentifier =
    withSuffix(Identifier.defaultSeparator, suffix)

  def withSuffix(separator: String, suffix: String): SuffixedIdentifier = this match {
    case _: SimpleIdentifier => SuffixedIdentifier(name, separator, suffix)
    case si: SuffixedIdentifier => si.copy(separator = separator, suffix = suffix)
  }
}

/* TODO: Remove object Identifier, make SimpleIdentifier's and SuffixedIdentifier's
 *       constructors private, and force all clients to go through an
 *       IdentifierFactory.
 */

object Identifier {
  val defaultSeparator = "@"

  def apply(name: String): Identifier = SimpleIdentifier(name)

  def apply(prefix: String, separator: String, suffix: String): Identifier =
    SuffixedIdentifier(prefix, separator, suffix)
}

case class SimpleIdentifier(name: String) extends Identifier {
  def rename(fn: String => String) = SimpleIdentifier(fn(name))
  override val toString = name
}

case class SuffixedIdentifier(prefix: String, separator: String, suffix: String)
    extends Identifier {

  val name = s"$prefix$separator$suffix"
  def rename(fn: String => String) = SuffixedIdentifier(fn(prefix), separator, suffix)
  override val toString = name
}

trait IdentifierFactory {
  def separator: String
  def fresh(name: String): Identifier
}

class DefaultIdentifierFactory(namespace: String)
    extends IdentifierFactory
       with StatefulComponent {

  private val ids: Counter = new Counter

  val separator = Identifier.defaultSeparator

  def fresh(name: String): Identifier = {
    SuffixedIdentifier(name, separator, s"${ids.next()}$separator$namespace")
  }

  def start(): Unit = {}
  def reset(): Unit = { ids.reset() }
  def stop(): Unit = {}
}
