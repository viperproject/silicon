// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package decider

import com.microsoft.z3
import viper.silicon.state.terms._
import viper.silicon.state.Identifier

import scala.collection.mutable

class TermToZ3Converter(private val ctx: z3.Context,
                        private val renderSortName: Sort => String,
                        private val renderIdentifier: Identifier => String,
                        private val renderTerm: Term => String) {
  private val sortMap: mutable.Map[String, (z3.Symbol, z3.Sort)] = mutable.Map()
  // The same function symbol can be used in multiple functions declarations that differ for the signature.
  private val funcs: mutable.Buffer[(z3.Symbol, z3.FuncDecl)] = mutable.Buffer()
  private var cachedSortSymbols: Array[z3.Symbol] = Array()
  private var cachedSortTypes: Array[z3.Sort] = Array()
  private var cachedFuncSymbols: Array[z3.Symbol] = Array()
  private var cachedFuncDecls: Array[z3.FuncDecl] = Array()

  // Initialize with builtin sorts
  registerSort("Bool", _ => ctx.getBoolSort)
  registerSort("Int", _ => ctx.getIntSort)
  registerSort("Real", _ => ctx.getRealSort)

  def registerSort(name: String, mkSort: (z3.Symbol) => z3.Sort): z3.Sort = {
    if (sortMap.contains(name)) {
      throw new IllegalArgumentException(s"A sort named '$name' has already been registered.")
    }
    val symbol = ctx.mkSymbol(name)
    val sort = mkSort(symbol)
    sortMap(name) = (symbol, sort)
    // Invalidate cache
    cachedSortSymbols = null
    cachedSortTypes = null
    sort
  }

  def getSort(name: String): z3.Sort = {
    sortMap(name)._2
  }

  def registerFuncDecl(name: String, mkFunDecl: (z3.Symbol) => z3.FuncDecl): z3.FuncDecl = {
    val symbol = ctx.mkSymbol(name)
    val funcDecl = mkFunDecl(symbol)
    funcs.append((symbol, funcDecl))
    // Invalidate cache
    cachedFuncSymbols = null
    cachedFuncDecls = null
    funcDecl
  }

  /// Interpret an SMTLIB2 command, returning the first parsed boolean expressions.
  def parseCommand(command: String): z3.BoolExpr = {
    if (cachedSortSymbols == null || cachedSortTypes == null) {
      val sorts = sortMap.values.toSeq
      cachedSortSymbols = sorts.map(_._1).toArray
      cachedSortTypes = sorts.map(_._2).toArray
    }
    if (cachedFuncSymbols == null || cachedFuncDecls == null) {
      cachedFuncSymbols = funcs.map(_._1).toArray
      cachedFuncDecls = funcs.map(_._2).toArray
    }
    ctx.parseSMTLIB2String(
      command.replace("\n", " ").replace("\t", " "),
      cachedSortSymbols,
      cachedSortTypes,
      cachedFuncSymbols,
      cachedFuncDecls
    ).head
  }

  def declare(decl: Decl): Option[z3.BoolExpr] = {
    decl match {
      case SortDecl(sort: Sort) =>
        val name = renderSortName(sort)
        registerSort(name, ctx.mkUninterpretedSort)
        None

      case FunctionDecl(fun: Function) =>
        val name: String = renderIdentifier(fun.id)
        val argSortNames = fun.argSorts.map(renderSortName).filter(_ != "")
        val z3ArgSorts = argSortNames.map(sortMap).map(_._2).toArray
        val returnSortName = renderSortName(fun.resultSort)
        val z3ResultSort = sortMap(returnSortName)._2
        registerFuncDecl(name, ctx.mkFuncDecl(_, z3ArgSorts, z3ResultSort))
        None

      case swd @ SortWrapperDecl(from, to) =>
        val name: String = renderIdentifier(swd.id)
        val argSortName = renderSortName(from)
        val z3ArgSort = sortMap(argSortName)._2
        val returnSortName = renderSortName(to)
        val z3ResultSort = sortMap(returnSortName)._2
        registerFuncDecl(name, ctx.mkFuncDecl(_, z3ArgSort, z3ResultSort))
        None

      case MacroDecl(id, args, body) =>
        val name: String = renderIdentifier(id)
        val argSortNames = args.map(_.sort).map(renderSortName)
        val z3ArgSorts = argSortNames.map(sortMap).map(_._2).toArray
        val resultSortName = renderSortName(body.sort)
        val z3ResultSort = sortMap(resultSortName)._2
        registerFuncDecl(name, ctx.mkFuncDecl(_, z3ArgSorts, z3ResultSort))

        // Convert a Term to a Z3 expression by generating and parsing a SMTLIB2 command.
        val paramNames = args.map(_.id).map(renderIdentifier)
        val vars = args.map(p => s"(${p.id.name} ${renderSortName(p.sort)})")
        val triggers = s":pattern (($name ${paramNames.mkString(" ")}))"
        Some(parseCommand(
          s"(assert (forall (${vars.mkString(" ")}) (! (= ($name ${paramNames.mkString(" ")}) ${renderTerm(body)}) $triggers)))"
        ))
    }
  }
}
