package viper.silicon.state.chunks

import viper.silicon
import viper.silicon.dependencyAnalysis.DependencyAnalysisInfos
import viper.silicon.resources.BaseID
import viper.silicon.rules.InverseFunctions
import viper.silicon.state.terms.{MagicWandSnapshot, Term, Var}
import viper.silver.ast

trait ChunkFactory {
  def createBasicChunk(resourceID: BaseID,
                       id: BasicChunkIdentifier,
                       args: Seq[Term],
                       argsExp: Option[Seq[ast.Exp]],
                       snap: Term,
                       snapExp: Option[ast.Exp],
                       perm: Term,
                       permExp: Option[ast.Exp],
                       analysisInfos: DependencyAnalysisInfos,
                       isExhale: Boolean = false): BasicChunk

  def createQuantifiedFieldChunk(id: BasicChunkIdentifier,
                                 fvf: Term,
                                 condition: Term,
                                 conditionExp: Option[ast.Exp],
                                 permValue: Term,
                                 permValueExp: Option[ast.Exp],
                                 invs: Option[InverseFunctions],
                                 singletonRcvr: Option[Term],
                                 singletonRcvrExp: Option[ast.Exp],
                                 hints: Seq[Term] = Nil,
                                 analysisInfos: DependencyAnalysisInfos,
                                 isExhale: Boolean = false): QuantifiedFieldChunk

  def createQuantifiedPredicateChunk(id: BasicChunkIdentifier,
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
                                     analysisInfos: DependencyAnalysisInfos,
                                     isExhale: Boolean = false): QuantifiedPredicateChunk

  def createQuantifiedMagicWandChunk(id: MagicWandIdentifier,
                                     quantifiedVars: Seq[Var],
                                     quantifiedVarExps: Option[Seq[ast.LocalVarDecl]],
                                     wsf: Term,
                                     perm: Term,
                                     permExp: Option[ast.Exp],
                                     invs: Option[InverseFunctions],
                                     singletonArgs: Option[Seq[Term]],
                                     singletonArgExps: Option[Seq[ast.Exp]],
                                     hints: Seq[Term] = Nil,
                                     analysisInfos: DependencyAnalysisInfos,
                                     isExhale: Boolean = false): QuantifiedMagicWandChunk

  def createMagicWandChunk(id: MagicWandIdentifier,
                           bindings: Map[ast.AbstractLocalVar, (Term, Option[ast.Exp])],
                           args: Seq[Term],
                           argsExp: Option[Seq[ast.Exp]],
                           snap: MagicWandSnapshot,
                           perm: Term,
                           permExp: Option[ast.Exp],
                           analysisInfos: DependencyAnalysisInfos,
                           isExhale: Boolean = false): MagicWandChunk

  def applyCondition(chunk: GeneralChunk, newCond: Term, newCondExp: Option[ast.Exp], analysisInfos: DependencyAnalysisInfos): GeneralChunk

  def permMinus(chunk: GeneralChunk, newPerm: Term, newPermExp: Option[ast.Exp], analysisInfos: DependencyAnalysisInfos): GeneralChunk
  def permMinus(chunk: QuantifiedBasicChunk, newPerm: Term, newPermExp: Option[ast.Exp], analysisInfos: DependencyAnalysisInfos): QuantifiedBasicChunk

  def permPlus(chunk: GeneralChunk, newPerm: Term, newPermExp: Option[ast.Exp], analysisInfos: DependencyAnalysisInfos, isExhale: Boolean=false): GeneralChunk

  def withPerm(chunk: GeneralChunk, newPerm: Term, newPermExp: Option[ast.Exp], analysisInfos: DependencyAnalysisInfos, isExhale: Boolean=false): GeneralChunk

  def withPermNonQuantifiedChunk(chunk: NonQuantifiedChunk, newPerm: Term, newPermExp: Option[ast.Exp], analysisInfos: DependencyAnalysisInfos, isExhale: Boolean=false): NonQuantifiedChunk

  def permScale(chunk: GeneralChunk, newPerm: Term, newPermExp: Option[ast.Exp], analysisInfos: DependencyAnalysisInfos, isExhale: Boolean=false): GeneralChunk

  def substitute(chunk: GeneralChunk, terms: silicon.Map[Term, Term], analysisInfos: DependencyAnalysisInfos, isExhale: Boolean=false): GeneralChunk

  def withSnapshotMap(chunk: QuantifiedChunk, snap: Term, analysisInfos: DependencyAnalysisInfos): QuantifiedChunk

  def withSnap(chunk: NonQuantifiedChunk, snap: Term, snapExp: Option[ast.Exp], analysisInfos: DependencyAnalysisInfos): NonQuantifiedChunk

}

class DefaultChunkFactory extends ChunkFactory {
  override def createBasicChunk(resourceID: BaseID,
                                id: BasicChunkIdentifier,
                                args: Seq[Term],
                                argsExp: Option[Seq[ast.Exp]],
                                snap: Term,
                                snapExp: Option[ast.Exp],
                                perm: Term,
                                permExp: Option[ast.Exp],
                                analysisInfos: DependencyAnalysisInfos,
                                isExhale: Boolean = false): BasicChunk =
    BasicChunk(resourceID, id, args, argsExp, snap, snapExp, perm, permExp)

  override def createQuantifiedFieldChunk(id: BasicChunkIdentifier,
                                          fvf: Term,
                                          condition: Term,
                                          conditionExp: Option[ast.Exp],
                                          permValue: Term,
                                          permValueExp: Option[ast.Exp],
                                          invs: Option[InverseFunctions],
                                          singletonRcvr: Option[Term],
                                          singletonRcvrExp: Option[ast.Exp],
                                          hints: Seq[Term] = Nil,
                                          analysisInfos: DependencyAnalysisInfos,
                                          isExhale: Boolean = false): QuantifiedFieldChunk =
    QuantifiedFieldChunk(id, fvf, condition, conditionExp, permValue, permValueExp, invs, singletonRcvr, singletonRcvrExp, hints)

  override def createQuantifiedPredicateChunk(id: BasicChunkIdentifier,
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
                                              analysisInfos: DependencyAnalysisInfos,
                                              isExhale: Boolean = false): QuantifiedPredicateChunk =
    QuantifiedPredicateChunk(id, quantifiedVars, quantifiedVarExps, psf, condition, conditionExp, permValue, permValueExp, invs, singletonArgs, singletonArgExps, hints)

  override def createQuantifiedMagicWandChunk(id: MagicWandIdentifier,
                                              quantifiedVars: Seq[Var],
                                              quantifiedVarExps: Option[Seq[ast.LocalVarDecl]],
                                              wsf: Term,
                                              perm: Term,
                                              permExp: Option[ast.Exp],
                                              invs: Option[InverseFunctions],
                                              singletonArgs: Option[Seq[Term]],
                                              singletonArgExps: Option[Seq[ast.Exp]],
                                              hints: Seq[Term] = Nil,
                                              analysisInfos: DependencyAnalysisInfos,
                                              isExhale: Boolean = false): QuantifiedMagicWandChunk =
    QuantifiedMagicWandChunk(id, quantifiedVars, quantifiedVarExps, wsf, perm, permExp, invs, singletonArgs, singletonArgExps, hints)

  override def createMagicWandChunk(id: MagicWandIdentifier,
                                    bindings: Map[ast.AbstractLocalVar, (Term, Option[ast.Exp])],
                                    args: Seq[Term],
                                    argsExp: Option[Seq[ast.Exp]],
                                    snap: MagicWandSnapshot,
                                    perm: Term,
                                    permExp: Option[ast.Exp],
                                    analysisInfos: DependencyAnalysisInfos,
                                    isExhale: Boolean = false): MagicWandChunk =
    MagicWandChunk(id, bindings, args, argsExp, snap, perm, permExp)

  def applyCondition(chunk: GeneralChunk, newCond: Term, newCondExp: Option[ast.Exp], analysisInfos: DependencyAnalysisInfos): GeneralChunk =
    chunk.applyCondition(newCond, newCondExp)

  def permMinus(chunk: GeneralChunk, newPerm: Term, newPermExp: Option[ast.Exp], analysisInfos: DependencyAnalysisInfos): GeneralChunk =
    chunk.permMinus(newPerm, newPermExp)

  def permMinus(chunk: QuantifiedBasicChunk, newPerm: Term, newPermExp: Option[ast.Exp], analysisInfos: DependencyAnalysisInfos): QuantifiedBasicChunk =
    chunk.permMinus(newPerm, newPermExp)

  def permPlus(chunk: GeneralChunk, newPerm: Term, newPermExp: Option[ast.Exp], analysisInfos: DependencyAnalysisInfos, isExhale: Boolean=false): GeneralChunk =
    chunk.permPlus(newPerm, newPermExp)

  def withPerm(chunk: GeneralChunk, newPerm: Term, newPermExp: Option[ast.Exp], analysisInfos: DependencyAnalysisInfos, isExhale: Boolean=false): GeneralChunk =
    chunk.withPerm(newPerm, newPermExp)

  def withPermNonQuantifiedChunk(chunk: NonQuantifiedChunk, newPerm: Term, newPermExp: Option[ast.Exp], analysisInfos: DependencyAnalysisInfos, isExhale: Boolean=false): NonQuantifiedChunk =
    chunk.withPerm(newPerm, newPermExp)

  def permScale(chunk: GeneralChunk, newPerm: Term, newPermExp: Option[ast.Exp], analysisInfos: DependencyAnalysisInfos, isExhale: Boolean=false): GeneralChunk =
    chunk.permScale(newPerm, newPermExp)

  def substitute(chunk: GeneralChunk, terms: silicon.Map[Term, Term], analysisInfos: DependencyAnalysisInfos, isExhale: Boolean=false): GeneralChunk =
    chunk.substitute(terms)

  def withSnapshotMap(chunk: QuantifiedChunk, snap: Term, analysisInfos: DependencyAnalysisInfos): QuantifiedChunk = chunk.withSnapshotMap(snap)

  def withSnap(chunk: NonQuantifiedChunk, snap: Term, snapExp: Option[ast.Exp], analysisInfos: DependencyAnalysisInfos): NonQuantifiedChunk = chunk.withSnap(snap, snapExp)

}
