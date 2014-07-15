/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon
package common

package object config {
  def wildcardToRegex(str: String) =
    str.replace(".", "\\.")
       .replace("?", ".?")
       .replace("*", ".*?")
       .replace("$", "\\$")
}
