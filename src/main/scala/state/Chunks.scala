/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.state

import viper.silicon.interfaces.state._
import viper.silicon.resources._
import viper.silicon.rules.InverseFunctions
import viper.silicon.state.terms._
import viper.silicon.state.terms.predef.`?r`
import viper.silicon.verifier.Verifier
import viper.silver.ast

case class BasicChunkIdentifier(name: String) extends ChunkIdentifer {
  override def toString = name
}

case class BasicChunk(resourceID: BaseID,
                      id: BasicChunkIdentifier,
                      args: Seq[Term],
                      snap: Term,
                      perm: Term)
    extends NonQuantifiedChunk {

  require(perm.sort == sorts.Perm, s"Permissions $perm must be of sort Perm, but found ${perm.sort}")
  resourceID match {
    case FieldID() => require(snap.sort != sorts.Snap, s"A field chunk's value ($snap) is not expected to be of sort Snap")
    case PredicateID() => require(snap.sort == sorts.Snap, s"A predicate chunk's snapshot ($snap) is expected to be of sort Snap, but found ${snap.sort}")
  }

  override def withPerm(newPerm: Term) = BasicChunk(resourceID, id, args, snap, newPerm)
  override def withSnap(newSnap: Term) = BasicChunk(resourceID, id, args, newSnap, perm)

  override lazy val toString = resourceID match {
    case FieldID() => s"${args.head}.$id -> $snap # $perm"
    case PredicateID() => s"$id($snap; ${args.mkString(",")}) # $perm"
  }
}

sealed trait QuantifiedChunk extends PermissionChunk {
  type Self <: QuantifiedChunk

  def name: String
  def snapshotMap: Term
  def singletonArguments: Option[Seq[Term]]
  def hints: Seq[Term]

  def valueAt(arguments: Seq[Term]): Term

  def duplicate(name: String = name,
                snapshotMap: Term = snapshotMap,
                perm: Term,
                singletonArguments: Option[Seq[Term]] = singletonArguments,
                hints: Seq[Term] = hints)
               : Self
}

/* TODO: Instead of using the singletonRcvr to differentiate between QP chunks that
 *       provide permissions to a single location and those providing permissions
 *       to potentially multiple locations, consider using regular, non-quantified
 *       chunks instead.
 */
case class QuantifiedFieldChunk(name: String,
                                fvf: Term,
                                perm: Term,
                                invs: Option[InverseFunctions],
                                initialCond: Option[Term],
                                singletonRcvr: Option[Term],
                                hints: Seq[Term] = Nil)
    extends QuantifiedChunk {

  assert(fvf.sort.isInstanceOf[terms.sorts.FieldValueFunction],
         s"Quantified chunk values must be of sort FieldValueFunction, but found value $fvf of sort ${fvf.sort}")

  assert(perm.sort == sorts.Perm, s"Permissions $perm must be of sort Perm, but found ${perm.sort}")

  type Self = QuantifiedFieldChunk

  def snapshotMap: Term = fvf
  def singletonArguments: Option[Seq[Term]] = singletonRcvr.map(Seq(_))

  def valueAt(rcvr: Term): Term = Lookup(name, fvf, rcvr)

  def valueAt(arguments: Seq[Term]): Term = {
    assert(arguments.length == 1)

    Lookup(name, fvf, arguments.head)
  }

  def +(perm: Term): QuantifiedFieldChunk = copy(perm = PermPlus(this.perm, perm))
  def -(perm: Term): QuantifiedFieldChunk = copy(perm = PermMinus(this.perm, perm))
  def \(perm: Term): QuantifiedFieldChunk = copy(perm = perm)

  override def toString = s"${terms.Forall} ${`?r`} :: ${`?r`}.$name -> $fvf # $perm"

  def duplicate(name: String,
                snapshotMap: Term,
                perm: Term,
                singletonArguments: Option[Seq[Term]],
                hints: Seq[Term])
               : Self = {

    copy(name, fvf, perm, invs, initialCond, singletonRcvr, hints)
  }
}

case class QuantifiedPredicateChunk(name: String,
                                    formalVars: Seq[Var],
                                    psf: Term,
                                    perm: Term,
                                    invs: Option[InverseFunctions],
                                    initialCond: Option[Term],
                                    singletonArgs: Option[Seq[Term]],
                                    hints: Seq[Term] = Nil)
    extends QuantifiedChunk {

  assert(psf.sort.isInstanceOf[terms.sorts.PredicateSnapFunction], s"Quantified predicate chunk values must be of sort PredicateSnapFunction ($psf), but found ${psf.sort}")
  assert(perm.sort == sorts.Perm, s"Permissions $perm must be of sort Perm, but found ${perm.sort}")

  type Self = QuantifiedPredicateChunk

  def snapshotMap: Term = psf
  def singletonArguments: Option[Seq[Term]] = singletonArgs

  def valueAt(args: Seq[Term]) = PredicateLookup(name, psf, args)

  def +(perm: Term): QuantifiedPredicateChunk = copy(perm = PermPlus(this.perm, perm))
  def -(perm: Term): QuantifiedPredicateChunk = copy(perm = PermMinus(this.perm, perm))
  def \(perm: Term): QuantifiedPredicateChunk = copy(perm = perm)

  override def toString = s"${terms.Forall}  ${formalVars.mkString(",")} :: $name(${formalVars.mkString(",")}) -> $psf # $perm"

  def duplicate(name: String,
                snapshotMap: Term,
                perm: Term,
                singletonArguments: Option[Seq[Term]],
                hints: Seq[Term])
               : Self = {

    copy(name, formalVars, psf, perm, invs, initialCond, singletonArgs, hints)
  }
}

case class MagicWandIdentifier(ghostFreeWand: ast.MagicWand) extends ChunkIdentifer {
  override def equals(obj: Any): Boolean = obj match {
    case w: MagicWandIdentifier => ghostFreeWand.structurallyMatches(w.ghostFreeWand, Verifier.program)
    case _ => false
  }
}

case class MagicWandChunk(id: MagicWandIdentifier,
                          bindings: Map[ast.AbstractLocalVar, Term],
                          args: Seq[Term],
                          snap: MagicWandSnapshot,
                          perm: Term)
    extends NonQuantifiedChunk {

  require(perm.sort == sorts.Perm, s"Permissions $perm must be of sort Perm, but found ${perm.sort}")

  override val resourceID = MagicWandID()

  override def withPerm(newPerm: Term) = MagicWandChunk(id, bindings, args, snap, newPerm)
  override def withSnap(newSnap: Term) = newSnap match {
    case s: MagicWandSnapshot => MagicWandChunk(id, bindings, args, s, perm)
    case _ => sys.error(s"MagicWand snapshot has to be of type MagicWandSnapshot but found ${newSnap.getClass}")
  }

  override lazy val toString: String = {
    val pos = id.ghostFreeWand.pos match {
      case rp: viper.silver.ast.HasLineColumn => s"${rp.line}:${rp.column}"
      case other => other.toString
    }

    s"wand@$pos[$snap; ${args.mkString(",")}]"
  }
}
