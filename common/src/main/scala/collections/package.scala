/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.common

package object collections {
  /** Computes the cross product (cartesian product) of a sequence of sequences.
    * Code taken from http://stackoverflow.com/a/8569263/491216.
    *
    * @param xs The sequence of sequences to compute the cross product of.
    * @tparam A Type of the inner sequence's elements.
    * @return The computed cross product.
    */
  def crossProduct[A](xs: Traversable[Traversable[A]]): Seq[Seq[A]] =
    xs.foldLeft(Vector(Vector.empty[A])) {
      (x, y) => for (a <- x; b <- y) yield a :+ b
    }
}
