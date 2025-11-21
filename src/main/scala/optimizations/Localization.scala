// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2025 ETH Zurich.

package viper.silicon.optimizations

import viper.silicon.state.State
import viper.silver.ast.Exp

abstract class LocalizationMap {
  // methodName -> (Hash computed by state and proof obligation -> list of axiom guards)
  protected val axiomMap = scala.collection.mutable.Map.empty[Int, Seq[String]]

  protected def obligationHash(exps: Seq[Exp], state: State): Int = {
    val defaultName = "DummyMember"
      (
        exps.toString(),
        state.currentMember.map(_.name).getOrElse(defaultName),
        exps.map(_.pos)
      ).hashCode()
  }

  def getExpGuards(exps: Seq[Exp], state: State): Seq[String] = {
    axiomMap.getOrElse(
      obligationHash(exps, state),
      Seq(ProofEssence.globalGuardName)
    )
  }

  def updateExpGuards(exps: Seq[Exp], state: State, axioms: Seq[String]): Unit
}

class UnionLocalizationMap extends LocalizationMap {
  def updateExpGuards(exps: Seq[Exp], state: State, axioms: Seq[String]): Unit = {
    axiomMap.update(obligationHash(exps, state),
      (axiomMap.getOrElse(
        obligationHash(exps, state),
        List()).toSet | axioms.toSet).toList
    )
  }
}


object ProofEssence {

  val globalGuardName = "$GlobalGuard"
  val guardVariableName = "$LocalGuardVar"

  private var lmap: LocalizationMap = new UnionLocalizationMap()

  def getExpGuards(exps: Seq[Exp], state: State): Seq[String] = {
    println(s"getGuards: ${exps}")
    lmap.getExpGuards(exps, state)
  }

  def getExpGuards(exp: Exp, state: State): Seq[String] = {
    println(s"getGuard: ${exp}")
    lmap.getExpGuards(List(exp), state)
  }

  def updateExpGuards(exps: Seq[Exp], state: State, axioms: Seq[String]): Unit = {
    println(s"updateGuards: ${exps}")
    lmap.updateExpGuards(exps, state, axioms)
  }

  def updateExpGuards(exp: Exp, state: State, axioms: Seq[String]): Unit = {
    println(s"updateGuard: ${exp}")
    lmap.updateExpGuards(List(exp), state, axioms)
  }
}
