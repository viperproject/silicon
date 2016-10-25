/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.state

import viper.silver.ast
import viper.silicon.interfaces.state.{Chunk, PermissionChunk}
import viper.silicon.state.terms.{Lookup, PredicateLookup, PermMinus, PermPlus, Term, Var, sorts}
import viper.silicon.state.terms.predef.`?r`
import viper.silicon.supporters.qps.InverseFunction
import viper.silicon.supporters.qps.PredicateInverseFunction

sealed abstract class BasicChunk(val name: String,
                                 val args: Seq[Term],
                                 val snap: Term,
                                 val perm: Term)
    extends PermissionChunk {

  type Self <: BasicChunk

  assert(perm.sort == sorts.Perm, s"Permissions $perm must be of sort Perm, but found ${perm.sort}")

  def duplicate(name: String = name, snap: Term = snap, args: Seq[Term] = args, perm: Term = perm): Self

  def +(perm: Term): Self = duplicate(perm = PermPlus(this.perm, perm))
  def -(perm: Term): Self = duplicate(perm = PermMinus(this.perm, perm))
  def \(perm: Term) = duplicate(perm = perm)
}

case class FieldChunk(rcvr: Term,
                      override val name: String,
                      override val snap: Term,
                      override val perm: Term)
    extends BasicChunk(name, Seq(rcvr), snap, perm) {

  type Self = FieldChunk

  assert(snap.sort != sorts.Snap, s"A field chunk's value ($snap) is not expected to be of sort Snap")

  @inline
  final def duplicate(name: String = name, snap: Term = snap, args: Seq[Term] = Seq(rcvr), perm: Term = perm) =
    copy(rcvr, name, snap, perm)

  override def toString = s"$rcvr.$name -> $snap # $perm"
}

case class PredicateChunk(override val name: String,
                          override val args: Seq[Term],
                          override val snap: Term,
                          override val perm: Term)
    extends BasicChunk(name, args, snap, perm) {

  type Self = PredicateChunk

  assert(snap.sort == sorts.Snap,
         s"A predicate chunk's snapshot ($snap) is expected to be of sort Snap, but found ${snap.sort}")

  @inline
  final def duplicate(name: String = name, snap: Term = snap, args: Seq[Term] = args, perm: Term = perm) =
    copy(name, args, snap, perm)

  override def toString = s"$name($snap; ${args.mkString(",")}) # $perm"
}

case class QuantifiedFieldChunk(name: String,
                                fvf: Term,
                                perm: Term,
                                inv: Option[InverseFunction],
                                initialCond: Option[Term],
                                singletonRcvr: Option[Term],
                                hints: Seq[Term] = Nil)
    extends PermissionChunk {

  assert(fvf.sort.isInstanceOf[terms.sorts.FieldValueFunction],
         s"Quantified chunk values must be of sort FieldValueFunction, but found value $fvf of sort ${fvf.sort}")

  assert(perm.sort == sorts.Perm, s"Permissions $perm must be of sort Perm, but found ${perm.sort}")

  def valueAt(rcvr: Term) = Lookup(name, fvf, rcvr)

  def +(perm: Term) = copy(perm = PermPlus(this.perm, perm))
  def -(perm: Term) = copy(perm = PermMinus(this.perm, perm))
  def \(perm: Term) = copy(perm = perm)

  override def toString = s"${terms.Forall} ${`?r`} :: ${`?r`}.$name -> $fvf # $perm"
}

case class QuantifiedPredicateChunk(name: String,
                                    formalVars: Seq[Var],
                                    psf: Term,
                                    perm: Term,
                                    inv: Option[PredicateInverseFunction],
                                    initialCond: Option[Term],
                                    singletonArgs: Option[Seq[Term]],
                                    hints: Seq[Term] = Nil)
  extends PermissionChunk {

  assert(psf.sort.isInstanceOf[terms.sorts.PredicateSnapFunction], s"Quantified predicate chunk values must be of sort PredicateSnapFunction ($psf), but found ${psf.sort}")
  assert(perm.sort == sorts.Perm, s"Permissions $perm must be of sort Perm, but found ${perm.sort}")

  def valueAt(args: Seq[Term]) = PredicateLookup(name, psf, args, formalVars)

  def +(perm: Term) = copy(perm = PermPlus(this.perm, perm))
  def -(perm: Term) = copy(perm = PermMinus(this.perm, perm))
  def \(perm: Term) = copy(perm = perm)

  override def toString = s"${terms.Forall}  ${formalVars.mkString(",")} :: $name(${formalVars.mkString(",")}) -> $psf # $perm"
}

case class MagicWandChunk(ghostFreeWand: ast.MagicWand,
                          bindings: Map[ast.AbstractLocalVar, Term],
                          evaluatedTerms: Seq[Term])
    extends Chunk {

  override lazy val toString = {
    val pos = ghostFreeWand.pos match {
      case rp: viper.silver.ast.HasLineColumn => s"${rp.line}:${rp.column}"
      case other => other.toString
    }

    s"wand@$pos[${evaluatedTerms.mkString(",")}]"
  }
}
