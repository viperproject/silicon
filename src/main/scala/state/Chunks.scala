// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.state

import viper.silver.ast
import viper.silicon.interfaces.state._
import viper.silicon.resources._
import viper.silicon.rules.InverseFunctions
import viper.silicon.state.terms._
import viper.silicon.state.terms.predef.`?r`

object ChunkIdentifier {
  def apply(from: ast.Resource, program: ast.Program): ChunkIdentifer = {
    from match {
      case f: ast.Field => BasicChunkIdentifier(f.name)
      case p: ast.Predicate => BasicChunkIdentifier(p.name)
      case w: ast.MagicWand => MagicWandIdentifier(w, program)
    }
  }
}

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
  //resourceID match {
    //case FieldID => require(snap.sort != sorts.Snap, s"A field chunk's value ($snap) is not expected to be of sort Snap")
    //case PredicateID => require(snap.sort == sorts.Snap, s"A predicate chunk's snapshot ($snap) is expected to be of sort Snap, but found ${snap.sort}")
  //}

  override def applyCondition(newCond: Term) = withPerm(Ite(newCond, perm, NoPerm))
  override def permMinus(newPerm: Term) = withPerm(PermMinus(perm, newPerm))
  override def permPlus(newPerm: Term) = withPerm(PermPlus(perm, newPerm))
  override def withPerm(newPerm: Term) = BasicChunk(resourceID, id, args, snap, newPerm)

  override def withArgs(args: Seq[Term]) = BasicChunk(resourceID, id, args, snap, perm)
  override def withSnap(newSnap: Term) = BasicChunk(resourceID, id, args, newSnap, perm)

  override lazy val toString = resourceID match {
    case FieldID => s"${args.head}.$id -> $snap # $perm"
    case PredicateID => s"$id($snap; ${args.mkString(",")}) # $perm"
  }
  override def addEquality(t1: Term, t2: Term) = {
    BasicChunk(resourceID, id, args.map(_.replace(t1, t2)), snap.replace(t1, t2), perm.replace(t1, t2))
  }
}

sealed trait QuantifiedBasicChunk extends QuantifiedChunk {
  override val id: ChunkIdentifer

  override def applyCondition(newCond: Term): QuantifiedBasicChunk
  override def permMinus(perm: Term): QuantifiedBasicChunk
  override def permPlus(perm: Term): QuantifiedBasicChunk
  def withPerm(perm: Term): QuantifiedBasicChunk
  override def withSnapshotMap(snap: Term): QuantifiedBasicChunk
  def singletonArguments: Option[Seq[Term]]
  def hints: Seq[Term]
}

/* TODO: Instead of using the singletonRcvr to differentiate between QP chunks that
 *       provide permissions to a single location and those providing permissions
 *       to potentially multiple locations, consider using regular, non-quantified
 *       chunks instead.
 */
case class QuantifiedFieldChunk(id: BasicChunkIdentifier,
                                fvf: Term,
                                condition: Term,
                                permValue: Term,
                                invs: Option[InverseFunctions],
                                singletonRcvr: Option[Term],
                                hints: Seq[Term] = Nil)
    extends QuantifiedBasicChunk {

  require(fvf.sort.isInstanceOf[terms.sorts.FieldValueFunction],
         s"Quantified chunk values must be of sort FieldValueFunction, but found value $fvf of sort ${fvf.sort}")
  require(permValue.sort == sorts.Perm, s"Permissions $permValue must be of sort Perm, but found ${permValue.sort}")

  override val resourceID = FieldID
  override val quantifiedVars = Seq(`?r`)
  override val perm = Ite(condition, permValue, NoPerm)

  override def snapshotMap: Term = fvf
  override def singletonArguments: Option[Seq[Term]] = singletonRcvr.map(Seq(_))

  def valueAt(rcvr: Term): Term = Lookup(id.name, fvf, rcvr)

  override def valueAt(arguments: Seq[Term]): Term = {
    require(arguments.length == 1)

    Lookup(id.name, fvf, arguments.head)
  }

  override def applyCondition(newCond: Term) = QuantifiedFieldChunk(id, fvf, terms.And(newCond, condition), permValue, invs, singletonRcvr, hints)
  override def permMinus(newPerm: Term) = QuantifiedFieldChunk(id, fvf, condition, PermMinus(permValue, newPerm), invs, singletonRcvr, hints)
  override def permPlus(newPerm: Term) = QuantifiedFieldChunk(id, fvf, condition, PermPlus(permValue, newPerm), invs, singletonRcvr, hints)
  override def withSnapshotMap(newFvf: Term) = QuantifiedFieldChunk(id, newFvf, condition, permValue, invs, singletonRcvr, hints)
  override def withPerm(newPerm: Term) = {
    // TODO: This implementation only replaces permValue, so if the caller assumes that it'll set the perm value period, it is
    // only correct if newPerm is zero when condition is false.
    QuantifiedFieldChunk(id, fvf, condition, newPerm, invs, singletonRcvr, hints)
  }

  override lazy val toString = s"${terms.Forall} ${`?r`} :: ${`?r`}.$id -> $fvf # $perm"
}

case class QuantifiedPredicateChunk(id: BasicChunkIdentifier,
                                    quantifiedVars: Seq[Var],
                                    psf: Term,
                                    condition: Term,
                                    permValue: Term,
                                    invs: Option[InverseFunctions],
                                    singletonArgs: Option[Seq[Term]],
                                    hints: Seq[Term] = Nil)
    extends QuantifiedBasicChunk {

  require(psf.sort.isInstanceOf[terms.sorts.PredicateSnapFunction], s"Quantified predicate chunk values must be of sort PredicateSnapFunction ($psf), but found ${psf.sort}")
  require(permValue.sort == sorts.Perm, s"Permissions $permValue must be of sort Perm, but found ${permValue.sort}")

  override val resourceID = PredicateID
  override val perm = Ite(condition, permValue, NoPerm)

  override def snapshotMap: Term = psf
  override def singletonArguments: Option[Seq[Term]] = singletonArgs

  override def valueAt(args: Seq[Term]) = PredicateLookup(id.name, psf, args)

  override def applyCondition(newCond: Term) = QuantifiedPredicateChunk(id, quantifiedVars, psf, terms.And(newCond, condition), permValue, invs, singletonArgs, hints)
  override def permMinus(newPerm: Term) = QuantifiedPredicateChunk(id, quantifiedVars, psf, condition, PermMinus(permValue, newPerm), invs, singletonArgs, hints)
  override def permPlus(newPerm: Term) = QuantifiedPredicateChunk(id, quantifiedVars, psf, condition, PermPlus(permValue, newPerm), invs, singletonArgs, hints)
  override def withPerm(newPerm: Term) = QuantifiedPredicateChunk(id, quantifiedVars, psf, condition, newPerm, invs, singletonArgs, hints)

  override def withSnapshotMap(newPsf: Term) = QuantifiedPredicateChunk(id, quantifiedVars, newPsf, condition, permValue, invs, singletonArgs, hints)
  override lazy val toString = s"${terms.Forall} ${quantifiedVars.mkString(",")} :: $id(${quantifiedVars.mkString(",")}) -> $psf # $perm"
}

case class QuantifiedMagicWandChunk(id: MagicWandIdentifier,
                                    quantifiedVars: Seq[Var],
                                    wsf: Term,
                                    perm: Term,
                                    invs: Option[InverseFunctions],
                                    singletonArgs: Option[Seq[Term]],
                                    hints: Seq[Term] = Nil)
    extends QuantifiedBasicChunk {

  require(wsf.sort.isInstanceOf[terms.sorts.PredicateSnapFunction] && wsf.sort.asInstanceOf[terms.sorts.PredicateSnapFunction].codomainSort == sorts.Snap, s"Quantified magic wand chunk values must be of sort MagicWandSnapFunction ($wsf), but found ${wsf.sort}")
  require(perm.sort == sorts.Perm, s"Permissions $perm must be of sort Perm, but found ${perm.sort}")

  override val resourceID = MagicWandID

  override def snapshotMap: Term = wsf
  override def singletonArguments: Option[Seq[Term]] = singletonArgs

  override def valueAt(args: Seq[Term]) = PredicateLookup(id.toString, wsf, args)
  override def applyCondition(newCond: Term) = withPerm(Ite(newCond, perm, NoPerm))
  override def permMinus(newPerm: Term) = withPerm(PermMinus(perm, newPerm))
  override def permPlus(newPerm: Term) = withPerm(PermPlus(perm, newPerm))
  def withPerm(newPerm: Term) = QuantifiedMagicWandChunk(id, quantifiedVars, wsf, newPerm, invs, singletonArgs, hints)
  override def withSnapshotMap(newWsf: Term) = QuantifiedMagicWandChunk(id, quantifiedVars, newWsf, perm, invs, singletonArgs, hints)

  override lazy val toString = s"${terms.Forall} ${quantifiedVars.mkString(",")} :: $id(${quantifiedVars.mkString(",")}) -> $wsf # $perm"
}

case class MagicWandIdentifier(ghostFreeWand: ast.MagicWand)(override val hashCode: Int) extends ChunkIdentifer {
  override def equals(obj: Any): Boolean = obj match {
    case w: MagicWandIdentifier => this.hashCode == w.hashCode
    case _ => false
  }

  override lazy val toString = s"wand@${hashCode.toString}"
}

object MagicWandIdentifier {
  def apply(wand: ast.MagicWand, program: ast.Program): MagicWandIdentifier = {
    val structureWand = wand.structure(program)
    val hashCode = program.magicWandStructures.indexOf(structureWand)
    MagicWandIdentifier(wand)(hashCode)
  }
}

case class MagicWandChunk(id: MagicWandIdentifier,
                          bindings: Map[ast.AbstractLocalVar, Term],
                          args: Seq[Term],
                          snap: MagicWandSnapshot,
                          perm: Term)
    extends NonQuantifiedChunk {

  require(perm.sort == sorts.Perm, s"Permissions $perm must be of sort Perm, but found ${perm.sort}")

  override val resourceID = MagicWandID

  override def applyCondition(newCond: Term) =
    withPerm(Ite(newCond, perm, NoPerm))

  override def permMinus(newPerm: Term) =
    withPerm(PermMinus(perm, newPerm))

  override def permPlus(newPerm: Term) =
    withPerm(PermPlus(perm, newPerm))

  override def withPerm(newPerm: Term) = MagicWandChunk(id, bindings, args, snap, newPerm)
  override def withSnap(newSnap: Term) = newSnap match {
    case s: MagicWandSnapshot => MagicWandChunk(id, bindings, args, s, perm)
    case _ => sys.error(s"MagicWand snapshot has to be of type MagicWandSnapshot but found ${newSnap.getClass}")
  }

  override def withArgs(args: Seq[Term]) = MagicWandChunk(id, bindings, args, snap, perm)

  override lazy val toString = {
    val pos = id.ghostFreeWand.pos match {
      case rp: viper.silver.ast.HasLineColumn => s"${rp.line}:${rp.column}"
      case other => other.toString
    }
    s"wand@$pos[$snap; ${args.mkString(", ")}]"
  }
}
