// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.state

import viper.silicon
import viper.silver.ast
import viper.silicon.interfaces.state._
import viper.silicon.resources._
import viper.silicon.rules.InverseFunctions
import viper.silicon.state.terms._
import viper.silicon.state.terms.predef.`?r`
import viper.silicon.verifier.Verifier

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
                      argsExp: Option[Seq[ast.Exp]],
                      snap: Term,
                      snapExp: Option[ast.Exp],
                      perm: Term,
                      permExp: Option[ast.Exp])
    extends NonQuantifiedChunk {

  require(perm.sort == sorts.Perm, s"Permissions $perm must be of sort Perm, but found ${perm.sort}")
  resourceID match {
    case FieldID => require(snap.sort != sorts.Snap, s"A field chunk's value ($snap) is not expected to be of sort Snap")
    case PredicateID => require(snap.sort == sorts.Snap, s"A predicate chunk's snapshot ($snap) is expected to be of sort Snap, but found ${snap.sort}")
  }

  override def applyCondition(newCond: Term, newCondExp: Option[ast.Exp]) =
    withPerm(Ite(newCond, perm, NoPerm), newCondExp.map(nce => ast.CondExp(nce, permExp.get, ast.NoPerm()())()))
  override def permMinus(newPerm: Term, newPermExp: Option[ast.Exp]) =
    withPerm(PermMinus(perm, newPerm), newPermExp.map(npe => ast.PermSub(permExp.get, npe)()))
  override def permPlus(newPerm: Term, newPermExp: Option[ast.Exp]) =
    withPerm(PermPlus(perm, newPerm), newPermExp.map(npe => ast.PermAdd(permExp.get, npe)()))

  override def permScale(newPerm: Term, newPermExp: Option[ast.Exp]) =
    withPerm(PermTimes(perm, newPerm), permExp.map(pe => ast.PermMul(pe, newPermExp.get)()))
  override def withPerm(newPerm: Term, newPermExp: Option[ast.Exp]) = BasicChunk(resourceID, id, args, argsExp, snap, snapExp, newPerm, newPermExp)
  override def withSnap(newSnap: Term, newSnapExp: Option[ast.Exp]) = BasicChunk(resourceID, id, args, argsExp, newSnap, newSnapExp, perm, permExp)

  override lazy val toString = resourceID match {
    case FieldID => s"${args.head}.$id -> $snap # $perm"
    case PredicateID => s"$id($snap; ${args.mkString(",")}) # $perm"
  }

  override def substitute(terms: silicon.Map[Term, Term]) = {
    copy(args = args.map(_.replace(terms)), snap = snap.replace(terms), perm = perm.replace(terms))
  }
}

sealed trait QuantifiedBasicChunk extends QuantifiedChunk {
  override val id: ChunkIdentifer
  override def applyCondition(newCond: Term, newCondExp: Option[ast.Exp]): QuantifiedBasicChunk
  override def permMinus(perm: Term, permExp: Option[ast.Exp]): QuantifiedBasicChunk
  override def permPlus(perm: Term, permExp: Option[ast.Exp]): QuantifiedBasicChunk
  override def withSnapshotMap(snap: Term): QuantifiedBasicChunk
  def singletonArguments: Option[Seq[Term]]
  def singletonArgumentExps: Option[Seq[ast.Exp]]
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
                                conditionExp: Option[ast.Exp],
                                permValue: Term,
                                permValueExp: Option[ast.Exp],
                                invs: Option[InverseFunctions],
                                singletonRcvr: Option[Term],
                                singletonRcvrExp: Option[ast.Exp],
                                hints: Seq[Term] = Nil)
    extends QuantifiedBasicChunk {

  require(fvf.sort.isInstanceOf[terms.sorts.FieldValueFunction],
         s"Quantified chunk values must be of sort FieldValueFunction, but found value $fvf of sort ${fvf.sort}")
  require(permValue.sort == sorts.Perm, s"Permissions $permValue must be of sort Perm, but found ${permValue.sort}")

  override val resourceID = FieldID
  override val quantifiedVars = Seq(`?r`)
  override val perm = Ite(condition, permValue, NoPerm)
  override val permExp: Option[ast.Exp] =  conditionExp.map(c => ast.CondExp(c, permValueExp.get, ast.NoPerm()())())
  override val quantifiedVarExps = if (Verifier.config.enableDebugging()) Some(Seq(ast.LocalVarDecl(`?r`.id.name, ast.Ref)())) else None

  override def snapshotMap: Term = fvf
  override def singletonArguments: Option[Seq[Term]] = singletonRcvr.map(Seq(_))

  override def singletonArgumentExps: Option[Seq[ast.Exp]] = singletonRcvrExp.map(Seq(_))

  def valueAt(rcvr: Term): Term = Lookup(id.name, fvf, rcvr)

  override def valueAt(arguments: Seq[Term]): Term = {
    require(arguments.length == 1)

    Lookup(id.name, fvf, arguments.head)
  }

  def withPerm(newPerm: Term, newPermExp: Option[ast.Exp]) =
    QuantifiedFieldChunk(id, fvf, condition, conditionExp, newPerm, newPermExp, invs, singletonRcvr, singletonRcvrExp, hints)
  override def applyCondition(newCond: Term, newCondExp: Option[ast.Exp]) =
    QuantifiedFieldChunk(id, fvf, terms.And(newCond, condition), newCondExp.map(nce => ast.And(nce, conditionExp.get)()), permValue, permValueExp, invs, singletonRcvr, singletonRcvrExp, hints)
  override def permMinus(newPerm: Term, newPermExp: Option[ast.Exp]) =
    withPerm(PermMinus(permValue, newPerm), newPermExp.map(npe => ast.PermSub(permValueExp.get, npe)()))
  override def permPlus(newPerm: Term, newPermExp: Option[ast.Exp]) =
    withPerm(PermPlus(permValue, newPerm), newPermExp.map(npe => ast.PermAdd(permValueExp.get, npe)()))

  override def permScale(newPerm: Term, newPermExp: Option[ast.Exp]) =
    withPerm(PermTimes(perm, newPerm), permExp.map(pe => ast.PermMul(pe, newPermExp.get)()))
  override def withSnapshotMap(newFvf: Term) =
    QuantifiedFieldChunk(id, newFvf, condition, conditionExp, permValue, permValueExp, invs, singletonRcvr, singletonRcvrExp, hints)

  override lazy val toString = s"${terms.Forall} ${`?r`} :: ${`?r`}.$id -> $fvf # $perm"

  override def substitute(terms: silicon.Map[Term, Term]): Chunk =
    copy(fvf = fvf.replace(terms), condition = condition.replace(terms), permValue = permValue.replace(terms),
      singletonRcvr = singletonRcvr.map(_.replace(terms)), hints = hints.map(_.replace(terms)), invs = invs.map(_.substitute(terms)))
}

case class QuantifiedPredicateChunk(id: BasicChunkIdentifier,
                                    quantifiedVars: Seq[Var],
                                    quantifiedVarExps: Option[Seq[ast.LocalVarDecl]],
                                    psf: Term,
                                    condition: Term,
                                    conditionExp: Option[ast.Exp],
                                    permValue: Term,
                                    permValueExp: Option[ast.Exp],
                                    invs: Option[InverseFunctions],
                                    singletonArgs: Option[Seq[Term]],
                                    singletonArgExps: Option[Seq[ast.Exp]],
                                    hints: Seq[Term] = Nil)
    extends QuantifiedBasicChunk {

  require(psf.sort.isInstanceOf[terms.sorts.PredicateSnapFunction], s"Quantified predicate chunk values must be of sort PredicateSnapFunction ($psf), but found ${psf.sort}")
  require(permValue.sort == sorts.Perm, s"Permissions $permValue must be of sort Perm, but found ${permValue.sort}")

  override val resourceID = PredicateID
  override val perm = Ite(condition, permValue, NoPerm)
  override val permExp = conditionExp.map(c => ast.CondExp(c, permValueExp.get, ast.NoPerm()())())

  override def snapshotMap: Term = psf
  override def singletonArguments: Option[Seq[Term]] = singletonArgs
  override def singletonArgumentExps: Option[Seq[ast.Exp]] = singletonArgExps

  override def valueAt(args: Seq[Term]) = PredicateLookup(id.name, psf, args)

  def withPerm(newPerm: Term, newPermExp: Option[ast.Exp]) =
    QuantifiedPredicateChunk(id, quantifiedVars, quantifiedVarExps, psf, condition, conditionExp, newPerm, newPermExp, invs, singletonArgs, singletonArgExps, hints)
  override def applyCondition(newCond: Term, newCondExp: Option[ast.Exp]) =
    QuantifiedPredicateChunk(id, quantifiedVars, quantifiedVarExps, psf, terms.And(newCond, condition), newCondExp.map(nce => ast.And(nce, conditionExp.get)()), permValue, permValueExp, invs, singletonArgs, singletonArgExps, hints)
  override def permMinus(newPerm: Term, newPermExp: Option[ast.Exp]) =
    withPerm(PermMinus(permValue, newPerm), newPermExp.map(npe => ast.PermSub(permValueExp.get, npe)()))
  override def permPlus(newPerm: Term, newPermExp: Option[ast.Exp]) =
    withPerm(PermPlus(permValue, newPerm), newPermExp.map(npe => ast.PermAdd(permValueExp.get, npe)()))

  override def permScale(newPerm: Term, newPermExp: Option[ast.Exp]) =
    withPerm(PermTimes(perm, newPerm), permExp.map(pe => ast.PermMul(pe, newPermExp.get)()))
  override def withSnapshotMap(newPsf: Term) =
    QuantifiedPredicateChunk(id, quantifiedVars, quantifiedVarExps, newPsf, condition, conditionExp, permValue, permValueExp, invs, singletonArgs, singletonArgExps, hints)

  override lazy val toString = s"${terms.Forall} ${quantifiedVars.mkString(",")} :: $id(${quantifiedVars.mkString(",")}) -> $psf # $perm"

  override def substitute(terms: silicon.Map[Term, Term]): Chunk =
    copy(psf = psf.replace(terms), condition = condition.replace(terms), permValue = permValue.replace(terms),
      singletonArgs = singletonArgs.map(_.map(_.replace(terms))), hints = hints.map(_.replace(terms)), invs = invs.map(_.substitute(terms)))
}

case class QuantifiedMagicWandChunk(id: MagicWandIdentifier,
                                    quantifiedVars: Seq[Var],
                                    quantifiedVarExps: Option[Seq[ast.LocalVarDecl]],
                                    wsf: Term,
                                    perm: Term,
                                    permExp: Option[ast.Exp],
                                    invs: Option[InverseFunctions],
                                    singletonArgs: Option[Seq[Term]],
                                    singletonArgExps: Option[Seq[ast.Exp]],
                                    hints: Seq[Term] = Nil)
    extends QuantifiedBasicChunk {

  require(wsf.sort.isInstanceOf[terms.sorts.PredicateSnapFunction] && wsf.sort.asInstanceOf[terms.sorts.PredicateSnapFunction].codomainSort == sorts.Snap, s"Quantified magic wand chunk values must be of sort MagicWandSnapFunction ($wsf), but found ${wsf.sort}")
  require(perm.sort == sorts.Perm, s"Permissions $perm must be of sort Perm, but found ${perm.sort}")

  override val resourceID = MagicWandID

  override def snapshotMap: Term = wsf
  override def singletonArguments: Option[Seq[Term]] = singletonArgs
  override def singletonArgumentExps: Option[Seq[ast.Exp]] = singletonArgExps

  override def valueAt(args: Seq[Term]) = PredicateLookup(id.toString, wsf, args)

  override def applyCondition(newCond: Term, newCondExp: Option[ast.Exp]) =
    withPerm(Ite(newCond, perm, NoPerm), newCondExp.map(nce => ast.CondExp(nce, permExp.get, ast.NoPerm()())()))
  override def permMinus(newPerm: Term, newPermExp: Option[ast.Exp]) =
    withPerm(PermMinus(perm, newPerm), newPermExp.map(npe => ast.PermSub(permExp.get, npe)()))
  override def permPlus(newPerm: Term, newPermExp: Option[ast.Exp]) =
    withPerm(PermPlus(perm, newPerm), newPermExp.map(npe => ast.PermAdd(permExp.get, npe)()))

  override def permScale(newPerm: Term, newPermExp: Option[ast.Exp]) =
    withPerm(PermTimes(perm, newPerm), permExp.map(pe => ast.PermMul(pe, newPermExp.get)()))
  def withPerm(newPerm: Term, newPermExp: Option[ast.Exp]) =
    QuantifiedMagicWandChunk(id, quantifiedVars, quantifiedVarExps, wsf, newPerm, newPermExp, invs, singletonArgs, singletonArgExps, hints)
  override def withSnapshotMap(newWsf: Term) =
    QuantifiedMagicWandChunk(id, quantifiedVars, quantifiedVarExps, newWsf, perm, permExp, invs, singletonArgs, singletonArgExps, hints)

  override lazy val toString = s"${terms.Forall} ${quantifiedVars.mkString(",")} :: $id(${quantifiedVars.mkString(",")}) -> $wsf # $perm"

  override def substitute(terms: silicon.Map[Term, Term]): Chunk =
    copy(wsf = wsf.replace(terms), perm = perm.replace(terms), singletonArgs = singletonArgs.map(_.map(_.replace(terms))),
      hints = hints.map(_.replace(terms)), invs = invs.map(_.substitute(terms)))
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
                          bindings: Map[ast.AbstractLocalVar, (Term, Option[ast.Exp])],
                          args: Seq[Term],
                          argsExp: Option[Seq[ast.Exp]],
                          snap: MagicWandSnapshot,
                          perm: Term,
                          permExp: Option[ast.Exp])
    extends NonQuantifiedChunk {

  require(perm.sort == sorts.Perm, s"Permissions $perm must be of sort Perm, but found ${perm.sort}")

  override val resourceID = MagicWandID

  override def applyCondition(newCond: Term, newCondExp: Option[ast.Exp]) =
    withPerm(Ite(newCond, perm, NoPerm), newCondExp.map(nce => ast.CondExp(nce, permExp.get, ast.NoPerm()())()))
  override def permMinus(newPerm: Term, newPermExp: Option[ast.Exp]) =
    withPerm(PermMinus(perm, newPerm), newPermExp.map(npe => ast.PermSub(permExp.get, npe)()))
  override def permPlus(newPerm: Term, newPermExp: Option[ast.Exp]) =
    withPerm(PermPlus(perm, newPerm), newPermExp.map(npe => ast.PermAdd(permExp.get, npe)()))

  override def permScale(newPerm: Term, newPermExp: Option[ast.Exp]) =
    withPerm(PermTimes(perm, newPerm), permExp.map(pe => ast.PermMul(pe, newPermExp.get)()))
  override def withPerm(newPerm: Term, newPermExp: Option[ast.Exp]) = MagicWandChunk(id, bindings, args, argsExp, snap, newPerm, newPermExp)

  override def withSnap(newSnap: Term, newSnapExp: Option[ast.Exp]) = {
    assert(newSnapExp.isEmpty)
    newSnap match {
      case s: MagicWandSnapshot => MagicWandChunk(id, bindings, args, argsExp, s, perm, permExp)
      case _ => sys.error(s"MagicWand snapshot has to be of type MagicWandSnapshot but found ${newSnap.getClass}")
    }
  }

  override lazy val toString = {
    val pos = id.ghostFreeWand.pos match {
      case rp: viper.silver.ast.HasLineColumn => s"${rp.line}:${rp.column}"
      case other => other.toString
    }
    s"wand@$pos[$snap; ${args.mkString(", ")}]"
  }

  override def substitute(terms: silicon.Map[Term, Term]) = {
    copy(args = args.map(_.replace(terms)), snap = snap.replace(terms).asInstanceOf[MagicWandSnapshot], perm = perm.replace(terms))
  }
}
