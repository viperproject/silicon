// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.resources

import viper.silicon.interfaces.state.QuantifiedChunk
import viper.silicon.state.terms
import viper.silicon.state.terms.{Term, Trigger, Var}
import viper.silicon.utils.ast.replaceVarsInExp
import viper.silver.ast

class QuantifiedPropertyInterpreter extends PropertyInterpreter {

  protected case class Info(chunk: QuantifiedChunk, args: Seq[Term], argsExp: Option[Seq[ast.Exp]], perms: Term, permsExp: Option[ast.Exp])

  private var argsUsed = false

  def buildPathConditionForChunk(chunk: QuantifiedChunk,
                                 property: Property,
                                 qvars: Seq[Var],
                                 qvarsExp: Option[Seq[ast.LocalVarDecl]],
                                 args: Seq[Term],
                                 argsExp: Option[Seq[ast.Exp]],
                                 perms: Term,
                                 permsExp: Option[ast.Exp],
                                 condition: Term,
                                 conditionExp: Option[ast.Exp],
                                 triggers: Seq[Trigger],
                                 qidPrefix: String)
                                : (Term, Option[ast.Exp]) = {
    val body = buildPathCondition(property.expression, Info(chunk, args, argsExp, perms, permsExp))
    val bodyTerm = body._1.replace(chunk.quantifiedVars, args)
    val bodyExp = body._2.map(b => replaceVarsInExp(b, chunk.quantifiedVarExps.get.map(_.name), argsExp.get))
    val description = s"$qidPrefix-${property.name}"
    val cond = if (argsUsed) condition else terms.True
    val condExp = if (argsUsed || conditionExp.isEmpty) conditionExp else Some(ast.TrueLit()(conditionExp.get.pos, conditionExp.get.info, conditionExp.get.errT))
    argsUsed = false
    val forallExp = bodyExp.map(b => ast.Forall(qvarsExp.get, Seq(), ast.Implies(condExp.get, b)())())
    (terms.Forall(qvars, terms.Implies(cond, bodyTerm), triggers, description), forallExp)
  }

  override protected def buildPermissionAccess(chunkPlaceholder: ChunkPlaceholder, info: Info) = (info.perms, info.permsExp)

  override protected def buildValueAccess(chunkPlaceholder: ChunkPlaceholder, info: Info) = {
    argsUsed = true
    (info.chunk.valueAt(info.args), Option.when(withExp)(???)) //  ast.FuncApp(s"valueAt", info.argsExp)(ast.NoPosition, ast.NoInfo, ast.InternalType, ast.NoTrafos))
  }

  override protected def extractArguments(chunkPlaceholder: ChunkPlaceholder,
                                          info: Info): (Seq[Term], Option[Seq[ast.Exp]]) = {
    argsUsed = true
    (info.args, info.argsExp)
  }

  override protected def buildCheck[K <: IteUsableKind]
                                   (condition: PropertyExpression[kinds.Boolean],
                                    thenDo: PropertyExpression[K],
                                    otherwise: PropertyExpression[K],
                                    info: Info) = {
    buildIfThenElse(condition, thenDo, otherwise, info)
  }

  override protected def buildForEach(chunkVariables: Seq[ChunkVariable],
                                      body: PropertyExpression[kinds.Boolean],
                                      info: Info) = {
    sys.error("ForEach clauses are not supported in quantified properties.")
  }
}
