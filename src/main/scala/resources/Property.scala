/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.resources

case class Property(expression: PropertyExpression[kinds.Boolean], name: String, description: String) {
  require(!name.contains(" "), "Property names may not contain whitespace characters.")

  override def toString = name
}
