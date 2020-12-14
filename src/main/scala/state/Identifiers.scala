// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.state

import viper.silver.components.StatefulComponent
import viper.silicon.state.terms.Sort
import viper.silicon.utils.Counter

sealed trait Identifier {
  def name: String
  def rename(fn: String => String): Identifier

  def withSuffix(suffix: String): SuffixedIdentifier =
    withSuffix(Identifier.defaultSeparator, suffix)

  def withSuffix(separator: String, suffix: String): SuffixedIdentifier
}

/* TODO: Remove object Identifier, make concrete identifiers' constructors private, and force all
         clients to go through an IdentifierFactory.
 */

object Identifier {
  val defaultSeparator = "@"

  def apply(name: String): Identifier = SimpleIdentifier(name)

  def apply(prefix: String, separator: String, suffix: String): SuffixedIdentifier =
    SuffixedIdentifier(prefix, separator, suffix)
}

case class SimpleIdentifier(name: String) extends Identifier {
  def rename(fn: String => String): SimpleIdentifier =
    SimpleIdentifier(fn(name))

  def withSuffix(separator: String, suffix: String): SuffixedIdentifier =
    SuffixedIdentifier(name, separator, suffix)

  override val toString: String = name
}

case class SuffixedIdentifier(prefix: Identifier, separator: String, suffix: String)
    extends Identifier {

  assert(
    !prefix.isInstanceOf[SuffixedIdentifier],
    s"A SuffixedIdentifier ($prefix) may not be the prefix of a SuffixedIdentifier")

  val name = s"$prefix$separator$suffix"

  def rename(fn: String => String): SuffixedIdentifier =
    SuffixedIdentifier(prefix.rename(fn), separator, suffix)

  def withSuffix(separator: String, suffix: String): SuffixedIdentifier =
    this.copy(separator = separator, suffix = suffix)

  override val toString: String = name
}

object SuffixedIdentifier extends ((String, String, String) => SuffixedIdentifier) {
  def apply(prefix: String, separator: String, suffix: String): SuffixedIdentifier =
    SuffixedIdentifier(SimpleIdentifier(prefix), separator, suffix)
}

case class SortBasedIdentifier(template: String, sorts: Seq[Sort]) extends Identifier {
  val name: String = template.format(sorts: _*)

  /** Note: Only renames the template, not the sorts; i.e. fn is only applied to the template. */
  def rename(fn: String => String): SortBasedIdentifier =
    SortBasedIdentifier(fn(template), sorts)

  def withSuffix(separator: String, suffix: String): SuffixedIdentifier =
    SuffixedIdentifier(this, separator, suffix)

  override val toString: String = name
}

trait IdentifierFactory {
  def separator: String
  def fresh(name: String): Identifier
}

class DefaultIdentifierFactory(namespace: String)
    extends IdentifierFactory
       with StatefulComponent {

  private val ids: Counter = new Counter

  val separator: String = Identifier.defaultSeparator

  def fresh(name: String): Identifier = {
    SuffixedIdentifier(name, separator, s"${ids.next()}$separator$namespace")
  }

  def start(): Unit = {}
  def reset(): Unit = { ids.reset() }
  def stop(): Unit = {}
}
