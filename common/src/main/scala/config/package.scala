/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.common

import java.util.{Comparator, Scanner}

package object config {
  def wildcardToRegex(str: String) =
    str.replace(".", "\\.")
       .replace("?", ".?")
       .replace("*", ".*?")
       .replace("$", "\\$")

  /* Inspired by http://sambarrow.com/compare-version-string-in-scala-java/ */
  object VersionComparator extends Comparator[String] {
    override def compare(version1: String, version2: String): Int = {
      val scanner1 = new Scanner(version1)
      val scanner2 = new Scanner(version2)

      scanner1.useDelimiter("\\.")
      scanner2.useDelimiter("\\.")

      while (scanner1.hasNextInt && scanner2.hasNextInt) {
        val component1 = scanner1.nextInt
        val component2 = scanner2.nextInt

        if (component1 > component2)
          return 1
        else if (component1 < component2)
          return -1
      }

      if (scanner1.hasNextInt) 1
      else if (scanner2.hasNextInt) -1
      else 0
    }
  }

  final case class Version(version: String) {
    def >(other: Version) = VersionComparator.compare(version, other.version) == 1
    def >=(other: Version) = VersionComparator.compare(version, other.version) >= 0
    def <(other: Version) = VersionComparator.compare(version, other.version) == -1
    def <=(other: Version) = VersionComparator.compare(version, other.version) <= 0
    def ==(other: Version) = version == other.version
    def ^(other: Version) = version.startsWith(s"$other.") || this == other

    override val toString = version
  }
}
