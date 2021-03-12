// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package rpi

object Names {
  /**
    * The prefix used for precondition predicates.
    */
  val precondition = "pre"

  /**
    * The prefix used for postcondition predicates.
    */
  val postcondition = "post"

  /**
    * The prefix used for invariant predicates.
    */
  val invariant = "inv"

  val snapshot = "s"

  val permission = "p"

  /**
    * The name used for the recursive predicate.
    */
  val recursive = "P"

  val appendLemma = "append_lemma"

  val downAnnotation = "__down__"

  val upAnnotation = "__up__"

  val allAnnotations = Seq(
    downAnnotation,
    upAnnotation)

  /**
    * Returns whether the given name corresponds to an annotation.
    *
    * @param name The name.
    * @return True if the name corresponds to an annotation.
    */
  def isAnnotation(name: String): Boolean =
    allAnnotations.contains(name)

  def isRecursive(name: String): Boolean =
    name == recursive
}