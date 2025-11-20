// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.state

import viper.silicon.dependencyAnalysis.AnalysisInfo
import viper.silicon.interfaces.state._
import viper.silicon.resources._
import viper.silicon.rules.InverseFunctions
import viper.silicon.state.terms._
import viper.silicon.state.terms.predef.`?r`
import viper.silicon.verifier.Verifier
import viper.silver.ast

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

object BasicChunk {
  private def apply(resourceID: BaseID, id: BasicChunkIdentifier,
            args: Seq[Term], argsExp: Option[Seq[ast.Exp]],
            snap: Term, snapExp: Option[ast.Exp],
            perm: Term, permExp: Option[ast.Exp]): BasicChunk = {
    new BasicChunk(resourceID, id, args, argsExp, snap, snapExp, perm, permExp)
  }

  def apply(resourceID: BaseID, id: BasicChunkIdentifier,
            args: Seq[Term], argsExp: Option[Seq[ast.Exp]],
            snap: Term, snapExp: Option[ast.Exp],
            perm: Term, permExp: Option[ast.Exp],
            analysisInfo: AnalysisInfo, isExhale: Boolean=false): BasicChunk = {
    analysisInfo.decider.registerChunk[BasicChunk]({finalPerm =>
      new BasicChunk(resourceID, id, args, argsExp, snap, snapExp, finalPerm, permExp)},
      perm, analysisInfo, isExhale)
  }
}

case class BasicChunk private (resourceID: BaseID,
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


  override protected def applyCondition(newCond: Term, newCondExp: Option[ast.Exp]): BasicChunk =
    withPerm(Ite(newCond, perm, NoPerm), newCondExp.map(nce => ast.CondExp(nce, permExp.get, ast.NoPerm()())()))
  override protected def permMinus(newPerm: Term, newPermExp: Option[ast.Exp]): BasicChunk =
    withPerm(PermMinus(perm, newPerm), newPermExp.map(npe => ast.PermSub(permExp.get, npe)()))
  override protected def permPlus(newPerm: Term, newPermExp: Option[ast.Exp]): BasicChunk =
    withPerm(PermPlus(perm, newPerm), newPermExp.map(npe => ast.PermAdd(permExp.get, npe)()))
  override protected def withPerm(newPerm: Term, newPermExp: Option[ast.Exp]): BasicChunk = new BasicChunk(resourceID, id, args, argsExp, snap, snapExp, newPerm, newPermExp)
  override protected def withSnap(newSnap: Term, newSnapExp: Option[ast.Exp]): BasicChunk = new BasicChunk(resourceID, id, args, argsExp, newSnap, newSnapExp, perm, permExp)

  override lazy val toString = resourceID match {
    case FieldID => s"${args.head}.$id -> $snap # $perm"
    case PredicateID => s"$id($snap; ${args.mkString(",")}) # $perm"
  }
}

object QuantifiedBasicChunk {
  def applyCondition(chunk: QuantifiedBasicChunk, newCond: Term, newCondExp: Option[ast.Exp], analysisInfo: AnalysisInfo): QuantifiedBasicChunk = {
    GeneralChunk.applyCondition(chunk, newCond, newCondExp, analysisInfo).asInstanceOf[QuantifiedBasicChunk]
  }
  def permMinus(chunk: QuantifiedBasicChunk, perm: Term, permExp: Option[ast.Exp], analysisInfo: AnalysisInfo): QuantifiedBasicChunk =
    GeneralChunk.permMinus(chunk, perm, permExp, analysisInfo).asInstanceOf[QuantifiedBasicChunk]
  def permPlus(chunk: QuantifiedBasicChunk, perm: Term, permExp: Option[ast.Exp], analysisInfo: AnalysisInfo): QuantifiedBasicChunk =
    GeneralChunk.permPlus(chunk, perm, permExp, analysisInfo).asInstanceOf[QuantifiedBasicChunk]
}

sealed trait QuantifiedBasicChunk extends QuantifiedChunk {
  override val id: ChunkIdentifer
  override protected def applyCondition(newCond: Term, newCondExp: Option[ast.Exp]): QuantifiedBasicChunk
  override protected def permMinus(perm: Term, permExp: Option[ast.Exp]): QuantifiedBasicChunk
  override protected def permPlus(perm: Term, permExp: Option[ast.Exp]): QuantifiedBasicChunk
  override protected def withSnapshotMap(snap: Term): QuantifiedBasicChunk
  def singletonArguments: Option[Seq[Term]]
  def singletonArgumentExps: Option[Seq[ast.Exp]]
  def hints: Seq[Term]
}

object QuantifiedFieldChunk {
  private def apply(id: BasicChunkIdentifier,
            fvf: Term,
            condition: Term,
            conditionExp: Option[ast.Exp],
            permValue: Term,
            permValueExp: Option[ast.Exp],
            invs: Option[InverseFunctions],
            singletonRcvr: Option[Term],
            singletonRcvrExp: Option[ast.Exp],
            hints: Seq[Term]): QuantifiedFieldChunk = {
    new QuantifiedFieldChunk(id, fvf, condition, conditionExp, permValue, permValueExp, invs, singletonRcvr, singletonRcvrExp, hints)
  }

  def apply(id: BasicChunkIdentifier,
            fvf: Term,
            condition: Term,
            conditionExp: Option[ast.Exp],
            permValue: Term,
            permValueExp: Option[ast.Exp],
            invs: Option[InverseFunctions],
            singletonRcvr: Option[Term],
            singletonRcvrExp: Option[ast.Exp],
            hints: Seq[Term] = Nil,
            analysisInfo: AnalysisInfo,
            isExhale: Boolean=false): QuantifiedFieldChunk = {
    analysisInfo.decider.registerChunk[QuantifiedFieldChunk]({perm =>
      new QuantifiedFieldChunk(id, fvf, condition, conditionExp, perm, permValueExp, invs, singletonRcvr, singletonRcvrExp, hints)},
      permValue, analysisInfo, isExhale)
  }
}

/* TODO: Instead of using the singletonRcvr to differentiate between QP chunks that
 *       provide permissions to a single location and those providing permissions
 *       to potentially multiple locations, consider using regular, non-quantified
 *       chunks instead.
 */
case class QuantifiedFieldChunk private(id: BasicChunkIdentifier,
                                fvf: Term,
                                condition: Term,
                                conditionExp: Option[ast.Exp],
                                permValue: Term,
                                permValueExp: Option[ast.Exp],
                                invs: Option[InverseFunctions],
                                singletonRcvr: Option[Term],
                                singletonRcvrExp: Option[ast.Exp],
                                hints: Seq[Term])
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

  override protected def withPerm(newPerm: Term, newPermExp: Option[ast.Exp]) =
    new QuantifiedFieldChunk(id, fvf, condition, conditionExp, newPerm, newPermExp, invs, singletonRcvr, singletonRcvrExp, hints)
  override protected def applyCondition(newCond: Term, newCondExp: Option[ast.Exp]) =
    new QuantifiedFieldChunk(id, fvf, terms.And(newCond, condition), newCondExp.map(nce => ast.And(nce, conditionExp.get)()), permValue, permValueExp, invs, singletonRcvr, singletonRcvrExp, hints)
  override protected def permMinus(newPerm: Term, newPermExp: Option[ast.Exp]) =
    withPerm(PermMinus(permValue, newPerm), newPermExp.map(npe => ast.PermSub(permValueExp.get, npe)()))
  override protected def permPlus(newPerm: Term, newPermExp: Option[ast.Exp]) =
    withPerm(PermPlus(permValue, newPerm), newPermExp.map(npe => ast.PermAdd(permValueExp.get, npe)()))
  override protected def withSnapshotMap(newFvf: Term) =
    new QuantifiedFieldChunk(id, newFvf, condition, conditionExp, permValue, permValueExp, invs, singletonRcvr, singletonRcvrExp, hints)

  override lazy val toString = s"${terms.Forall} ${`?r`} :: ${`?r`}.$id -> $fvf # $perm"
}

object QuantifiedPredicateChunk {
  private def apply(id: BasicChunkIdentifier,
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
            hints: Seq[Term]): QuantifiedPredicateChunk = {
    new QuantifiedPredicateChunk(id, quantifiedVars, quantifiedVarExps, psf, condition, conditionExp, permValue, permValueExp, invs, singletonArgs, singletonArgExps, hints)
  }


  def apply(id: BasicChunkIdentifier,
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
             hints: Seq[Term] = Nil,
            analysisInfo: AnalysisInfo,
            isExhale: Boolean=false): QuantifiedPredicateChunk = {
    analysisInfo.decider.registerChunk[QuantifiedPredicateChunk]({finalPerm =>
      new QuantifiedPredicateChunk(id, quantifiedVars, quantifiedVarExps, psf, condition, conditionExp, finalPerm, permValueExp, invs, singletonArgs, singletonArgExps, hints)},
      permValue, analysisInfo, isExhale)
  }
}


case class QuantifiedPredicateChunk private(id: BasicChunkIdentifier,
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
                                    hints: Seq[Term])
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

  override protected def withPerm(newPerm: Term, newPermExp: Option[ast.Exp]) =
    new QuantifiedPredicateChunk(id, quantifiedVars, quantifiedVarExps, psf, condition, conditionExp, newPerm, newPermExp, invs, singletonArgs, singletonArgExps, hints)
  override protected def applyCondition(newCond: Term, newCondExp: Option[ast.Exp]) =
    new QuantifiedPredicateChunk(id, quantifiedVars, quantifiedVarExps, psf, terms.And(newCond, condition), newCondExp.map(nce => ast.And(nce, conditionExp.get)()), permValue, permValueExp, invs, singletonArgs, singletonArgExps, hints)
  override protected def permMinus(newPerm: Term, newPermExp: Option[ast.Exp]) =
    withPerm(PermMinus(permValue, newPerm), newPermExp.map(npe => ast.PermSub(permValueExp.get, npe)()))
  override protected def permPlus(newPerm: Term, newPermExp: Option[ast.Exp]) =
    withPerm(PermPlus(permValue, newPerm), newPermExp.map(npe => ast.PermAdd(permValueExp.get, npe)()))
  override protected def withSnapshotMap(newPsf: Term) =
    new QuantifiedPredicateChunk(id, quantifiedVars, quantifiedVarExps, newPsf, condition, conditionExp, permValue, permValueExp, invs, singletonArgs, singletonArgExps, hints)

  override lazy val toString = s"${terms.Forall} ${quantifiedVars.mkString(",")} :: $id(${quantifiedVars.mkString(",")}) -> $psf # $perm"
}

object QuantifiedMagicWandChunk {
  private def apply(id: MagicWandIdentifier,
            quantifiedVars: Seq[Var],
            quantifiedVarExps: Option[Seq[ast.LocalVarDecl]],
            wsf: Term,
            perm: Term,
            permExp: Option[ast.Exp],
            invs: Option[InverseFunctions],
            singletonArgs: Option[Seq[Term]],
            singletonArgExps: Option[Seq[ast.Exp]],
            hints: Seq[Term]): QuantifiedMagicWandChunk = {
    new QuantifiedMagicWandChunk(id, quantifiedVars, quantifiedVarExps, wsf, perm, permExp, invs, singletonArgs, singletonArgExps, hints)
  }

  def apply(id: MagicWandIdentifier,
            quantifiedVars: Seq[Var],
            quantifiedVarExps: Option[Seq[ast.LocalVarDecl]],
            wsf: Term,
            perm: Term,
            permExp: Option[ast.Exp],
            invs: Option[InverseFunctions],
            singletonArgs: Option[Seq[Term]],
            singletonArgExps: Option[Seq[ast.Exp]],
            hints: Seq[Term] = Nil,
            analysisInfo: AnalysisInfo,
            isExhale: Boolean=false): QuantifiedMagicWandChunk = {
    analysisInfo.decider.registerChunk[QuantifiedMagicWandChunk]({finalPerm =>
      new QuantifiedMagicWandChunk(id, quantifiedVars, quantifiedVarExps, wsf, finalPerm, permExp, invs, singletonArgs, singletonArgExps, hints)},
      perm, analysisInfo, isExhale)
  }
}

case class QuantifiedMagicWandChunk private(id: MagicWandIdentifier,
                                    quantifiedVars: Seq[Var],
                                    quantifiedVarExps: Option[Seq[ast.LocalVarDecl]],
                                    wsf: Term,
                                    perm: Term,
                                    permExp: Option[ast.Exp],
                                    invs: Option[InverseFunctions],
                                    singletonArgs: Option[Seq[Term]],
                                    singletonArgExps: Option[Seq[ast.Exp]],
                                    hints: Seq[Term])
    extends QuantifiedBasicChunk {

  require(wsf.sort.isInstanceOf[terms.sorts.PredicateSnapFunction] && wsf.sort.asInstanceOf[terms.sorts.PredicateSnapFunction].codomainSort == sorts.Snap, s"Quantified magic wand chunk values must be of sort MagicWandSnapFunction ($wsf), but found ${wsf.sort}")
  require(perm.sort == sorts.Perm, s"Permissions $perm must be of sort Perm, but found ${perm.sort}")

  override val resourceID = MagicWandID

  override def snapshotMap: Term = wsf
  override def singletonArguments: Option[Seq[Term]] = singletonArgs
  override def singletonArgumentExps: Option[Seq[ast.Exp]] = singletonArgExps

  override def valueAt(args: Seq[Term]) = PredicateLookup(id.toString, wsf, args)

  override protected def applyCondition(newCond: Term, newCondExp: Option[ast.Exp]) =
    withPerm(Ite(newCond, perm, NoPerm), newCondExp.map(nce => ast.CondExp(nce, permExp.get, ast.NoPerm()())()))
  override protected def permMinus(newPerm: Term, newPermExp: Option[ast.Exp]) =
    withPerm(PermMinus(perm, newPerm), newPermExp.map(npe => ast.PermSub(permExp.get, npe)()))
  override protected def permPlus(newPerm: Term, newPermExp: Option[ast.Exp]) =
    withPerm(PermPlus(perm, newPerm), newPermExp.map(npe => ast.PermAdd(permExp.get, npe)()))
  override protected def withPerm(newPerm: Term, newPermExp: Option[ast.Exp]) =
    new QuantifiedMagicWandChunk(id, quantifiedVars, quantifiedVarExps, wsf, newPerm, newPermExp, invs, singletonArgs, singletonArgExps, hints)
  override protected def withSnapshotMap(newWsf: Term) =
    new QuantifiedMagicWandChunk(id, quantifiedVars, quantifiedVarExps, newWsf, perm, permExp, invs, singletonArgs, singletonArgExps, hints)

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

object MagicWandChunk {
  private def apply(id: MagicWandIdentifier,
            bindings: Map[ast.AbstractLocalVar, (Term, Option[ast.Exp])],
            args: Seq[Term],
            argsExp: Option[Seq[ast.Exp]],
            snap: MagicWandSnapshot,
            perm: Term,
            permExp: Option[ast.Exp]): MagicWandChunk = {
    new MagicWandChunk(id, bindings, args, argsExp, snap, perm, permExp)
  }

  def apply(id: MagicWandIdentifier,
            bindings: Map[ast.AbstractLocalVar, (Term, Option[ast.Exp])],
            args: Seq[Term],
            argsExp: Option[Seq[ast.Exp]],
            snap: MagicWandSnapshot,
            perm: Term,
            permExp: Option[ast.Exp],
            analysisInfo: AnalysisInfo,
            isExhale: Boolean=false): MagicWandChunk = {
    analysisInfo.decider.registerChunk[MagicWandChunk]({finalPerm =>
      new MagicWandChunk(id, bindings, args, argsExp, snap, finalPerm, permExp)},
      perm, analysisInfo, isExhale)
  }
}

case class MagicWandChunk private(id: MagicWandIdentifier,
                          bindings: Map[ast.AbstractLocalVar, (Term, Option[ast.Exp])],
                          args: Seq[Term],
                          argsExp: Option[Seq[ast.Exp]],
                          snap: MagicWandSnapshot,
                          perm: Term,
                          permExp: Option[ast.Exp])
    extends NonQuantifiedChunk {

  require(perm.sort == sorts.Perm, s"Permissions $perm must be of sort Perm, but found ${perm.sort}")

  override val resourceID = MagicWandID

  override protected def applyCondition(newCond: Term, newCondExp: Option[ast.Exp]) =
    withPerm(Ite(newCond, perm, NoPerm), newCondExp.map(nce => ast.CondExp(nce, permExp.get, ast.NoPerm()())()))
  override protected def permMinus(newPerm: Term, newPermExp: Option[ast.Exp]) =
    withPerm(PermMinus(perm, newPerm), newPermExp.map(npe => ast.PermSub(permExp.get, npe)()))
  override protected def permPlus(newPerm: Term, newPermExp: Option[ast.Exp]) =
    withPerm(PermPlus(perm, newPerm), newPermExp.map(npe => ast.PermAdd(permExp.get, npe)()))
  override protected def withPerm(newPerm: Term, newPermExp: Option[ast.Exp]) = new MagicWandChunk(id, bindings, args, argsExp, snap, newPerm, newPermExp)

  override protected def withSnap(newSnap: Term, newSnapExp: Option[ast.Exp]) = {
    assert(newSnapExp.isEmpty)
    newSnap match {
      case s: MagicWandSnapshot => new MagicWandChunk(id, bindings, args, argsExp, s, perm, permExp)
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
}
