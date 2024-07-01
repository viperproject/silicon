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
  resourceID match {
    case FieldID => require(snap.sort != sorts.Snap, s"A field chunk's value ($snap) is not expected to be of sort Snap")
    case PredicateID => require(snap.sort == sorts.Snap, s"A predicate chunk's snapshot ($snap) is expected to be of sort Snap, but found ${snap.sort}")
  }

  override def withPerm(newPerm: Term) = BasicChunk(resourceID, id, args, snap, newPerm)
  override def withSnap(newSnap: Term) = BasicChunk(resourceID, id, args, newSnap, perm)

  override lazy val toString = resourceID match {
    case FieldID => s"${args.head}.$id -> $snap # $perm"
    case PredicateID => s"$id($snap; ${args.mkString(",")}) # $perm"
  }
}

sealed trait QuantifiedBasicChunk extends QuantifiedChunk {
  override val id: ChunkIdentifer
  override def withPerm(perm: Term): QuantifiedBasicChunk
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
                                perm: Term,
                                invs: Option[InverseFunctions],
                                initialCond: Option[Term],
                                singletonRcvr: Option[Term],
                                hints: Seq[Term] = Nil)
    extends QuantifiedBasicChunk {

  require(fvf.sort.isInstanceOf[terms.sorts.FieldValueFunction],
         s"Quantified chunk values must be of sort FieldValueFunction, but found value $fvf of sort ${fvf.sort}")
  require(perm.sort == sorts.Perm, s"Permissions $perm must be of sort Perm, but found ${perm.sort}")

  override val resourceID = FieldID
  override val quantifiedVars = Seq(`?r`)

  override def snapshotMap: Term = fvf
  override def singletonArguments: Option[Seq[Term]] = singletonRcvr.map(Seq(_))

  def valueAt(rcvr: Term): Term = Lookup(id.name, fvf, rcvr)

  override def valueAt(arguments: Seq[Term]): Term = {
    require(arguments.length == 1)

    Lookup(id.name, fvf, arguments.head)
  }

  override def withPerm(newPerm: Term) = QuantifiedFieldChunk(id, fvf, newPerm, invs, initialCond, singletonRcvr, hints)
  override def withSnapshotMap(newFvf: Term) = QuantifiedFieldChunk(id, newFvf, perm, invs, initialCond, singletonRcvr, hints)

  override lazy val toString = s"${terms.Forall} ${`?r`} :: ${`?r`}.$id -> $fvf # $perm"
}

case class QuantifiedPredicateChunk(id: BasicChunkIdentifier,
                                    quantifiedVars: Seq[Var],
                                    psf: Term,
                                    perm: Term,
                                    invs: Option[InverseFunctions],
                                    initialCond: Option[Term],
                                    singletonArgs: Option[Seq[Term]],
                                    hints: Seq[Term] = Nil)
    extends QuantifiedBasicChunk {

  require(psf.sort.isInstanceOf[terms.sorts.PredicateSnapFunction], s"Quantified predicate chunk values must be of sort PredicateSnapFunction ($psf), but found ${psf.sort}")
  require(perm.sort == sorts.Perm, s"Permissions $perm must be of sort Perm, but found ${perm.sort}")

  override val resourceID = PredicateID

  override def snapshotMap: Term = psf
  override def singletonArguments: Option[Seq[Term]] = singletonArgs

  override def valueAt(args: Seq[Term]) = PredicateLookup(id.name, psf, args)

  override def withPerm(newPerm: Term) = QuantifiedPredicateChunk(id, quantifiedVars, psf, newPerm, invs, initialCond, singletonArgs, hints)
  override def withSnapshotMap(newPsf: Term) = QuantifiedPredicateChunk(id, quantifiedVars, newPsf, perm, invs, initialCond, singletonArgs, hints)

  override lazy val toString = s"${terms.Forall} ${quantifiedVars.mkString(",")} :: $id(${quantifiedVars.mkString(",")}) -> $psf # $perm"
}

case class QuantifiedMagicWandChunk(id: MagicWandIdentifier,
                                    quantifiedVars: Seq[Var],
                                    wsf: Term,
                                    perm: Term,
                                    invs: Option[InverseFunctions],
                                    initialCond: Option[Term],
                                    singletonArgs: Option[Seq[Term]],
                                    hints: Seq[Term] = Nil)
    extends QuantifiedBasicChunk {

  require(wsf.sort.isInstanceOf[terms.sorts.PredicateSnapFunction] && wsf.sort.asInstanceOf[terms.sorts.PredicateSnapFunction].codomainSort == sorts.Snap, s"Quantified magic wand chunk values must be of sort Snap ($wsf), but found ${wsf.sort}")
  require(perm.sort == sorts.Perm, s"Permissions $perm must be of sort Perm, but found ${perm.sort}")

  override val resourceID = MagicWandID

  override def snapshotMap: Term = wsf
  override def singletonArguments: Option[Seq[Term]] = singletonArgs

  override def valueAt(args: Seq[Term]) = PredicateLookup(id.toString, wsf, args)

  override def withPerm(newPerm: Term) = QuantifiedMagicWandChunk(id, quantifiedVars, wsf, newPerm, invs, initialCond, singletonArgs, hints)
  override def withSnapshotMap(newWsf: Term) = QuantifiedMagicWandChunk(id, quantifiedVars, newWsf, perm, invs, initialCond, singletonArgs, hints)

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

  override def withPerm(newPerm: Term) = MagicWandChunk(id, bindings, args, snap, newPerm)
  override def withSnap(newSnap: Term) = newSnap match {
    case s: MagicWandSnapshot => MagicWandChunk(id, bindings, args, s, perm)
    case _ => sys.error(s"MagicWand snapshot has to be of type MagicWandSnapshot but found ${newSnap.getClass}")
  }

  override lazy val toString = {
    val pos = id.ghostFreeWand.pos match {
      case rp: viper.silver.ast.HasLineColumn => s"${rp.line}:${rp.column}"
      case other => other.toString
    }
    s"wand@$pos[$snap; ${args.mkString(", ")}]"
  }
}
