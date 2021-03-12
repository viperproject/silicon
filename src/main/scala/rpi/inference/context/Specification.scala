// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package rpi.inference.context

import rpi.Names
import viper.silver.ast

/**
  * Represents a specification that needs to be inferred.
  *
  * @param name       The name identifying the specification.
  * @param parameters The parameters for the specification.
  * @param atoms      The atomic predicates that may be used for the specification.
  * @param existing   The existing part of the specification.
  */
case class Specification(name: String,
                         parameters: Seq[ast.LocalVarDecl],
                         atoms: Seq[ast.Exp],
                         existing: Seq[ast.Exp] = Seq.empty) {
  /**
    * Returns the variables corresponding to the parameters.
    *
    * @return The variables.
    */
  lazy val variables: Seq[ast.LocalVar] =
    parameters.map { parameter => parameter.localVar }

  /**
    * Returns whether this is the specification corresponding to the recursive predicate.
    *
    * @return True if this is the specification corresponding to the recursive predicate.
    */
  def isRecursive: Boolean =
    name == Names.recursive

  /**
    * Returns an instance of this specification.
    *
    * @return The instance.
    */
  def asInstance: Instance =
    IdentityInstance(this)

  override def toString: String =
    s"$name(${parameters.map(_.name).mkString(", ")})"
}