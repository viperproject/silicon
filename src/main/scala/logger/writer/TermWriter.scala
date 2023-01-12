// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.logger.writer

import spray.json.{JsArray, JsNull, JsObject, JsString, JsValue}
import viper.silicon.state.Identifier
import viper.silicon.state.terms._

/**
  *
  */
object TermWriter {

  private def binary(op: String, lhs: JsValue, rhs: JsValue): JsValue =
    JsObject(
      "type" -> JsString("binary"),
      "op" -> JsString(op),
      "lhs" -> lhs,
      "rhs" -> rhs
    )

  private def unary(op: String, p: JsValue) =
    JsObject(
      "type" -> JsString("unary"),
      "op" -> JsString(op),
      "p" -> p
    )

  private def variable(id: Identifier, sort: Sort) =
    JsObject(
      "type" -> JsString("variable"),
      "id" -> JsString(id.name),
      "sort" -> toJSON(sort)
    )

  def toJSON(sort: Sort): JsValue = {
    def s(name: String, elementsSort: Sort) = JsObject(
      "id" -> JsString(name),
      "elementsSort" -> toJSON(elementsSort)
    )

    sort match {
      case sorts.Unit => JsObject("id" -> JsString("Unit"))
      case sorts.Seq(elementsSort) => s("Seq", elementsSort)
      case sorts.Set(elementsSort) => s("Set", elementsSort)
      case sorts.Multiset(elementsSort) => s("Multiset", elementsSort)
      case sorts.UserSort(id) => JsObject("id" -> JsString("UserSort"), "name" -> JsString(id.name))
      case sorts.FieldValueFunction(codomainSort, fieldName) => JsObject("id" -> JsString("FVF"),
        "fieldName" -> JsString(fieldName), "elementSort" -> toJSON(codomainSort))
      case sorts.PredicateSnapFunction(codomainSort, predName) => JsObject("id" -> JsString("PSF"),
        "predName" -> JsString(predName), "elementSort" -> toJSON(codomainSort))
      case simple => JsObject("id" -> JsString(simple.id.name))
    }
  }

  def toJSON(term: Term): JsValue = term match {

    case b: BinaryOp[Term@unchecked] => binary(b.op, toJSON(b.p0), toJSON(b.p1))
    case u: UnaryOp[Term@unchecked] => unary(u.op, toJSON(u.p))

    // TODO: do we need triggers and isGlobal?
    case Quantification(quantifier, vars, body, _, name, _, _) =>
      JsObject(
        "type" -> JsString("quantification"),
        "quantifier" -> JsString(quantifier.toString),
        "vars" -> JsArray((vars map toJSON).toVector),
        "body" -> toJSON(body),
        "name" -> (if (name != null) JsString(name) else JsNull)
      )

    case a @ App(applicable, args) =>
      JsObject(
        "type" -> JsString("application"),
        "applicable" -> JsString(applicable.id.name),
        "args" -> JsArray((args map toJSON).toVector),
        "sort" -> toJSON(a.sort)
      )

    case Lookup(field, fieldValueFunction, receiver) =>
      JsObject(
        "type" -> JsString("lookup"),
        "field" -> JsString(field),
        "fieldValueFunction" -> toJSON(fieldValueFunction),
        "receiver" -> toJSON(receiver)
      )
    case PredicateLookup(predicate, predicateSnapFunction, args) =>
      JsObject(
        "type" -> JsString("predicateLookup"),
        "predicate" -> JsString(predicate),
        "predicateSnapFunction" -> toJSON(predicateSnapFunction),
        "args" -> JsArray((args map toJSON).toVector)
      )

    case And(terms) => JsObject("type" -> JsString("and"), "terms" -> JsArray((terms map toJSON).toVector))
    case Or(terms) => JsObject("type" -> JsString("or"), "terms" -> JsArray((terms map toJSON).toVector))

    case Distinct(symbols) =>
      JsObject(
        "type" -> JsString("distinct"),
        "symbols" -> JsArray((symbols map (s => JsString(s.id.name))).toVector)
      )

    case Ite(cond, thenBranch, elseBranch) =>
      JsObject(
        "type" -> JsString("ite"),
        "cond" -> toJSON(cond),
        "thenBranch" -> toJSON(thenBranch),
        "elseBranch" -> toJSON(elseBranch)
      )

    case Var(id, sort) => variable(id, sort)
    case SortWrapper(t, sort) =>
      JsObject(
        "type" -> JsString("sortWrapper"),
        "term" -> toJSON(t),
        "sort" -> toJSON(sort)
      )

    case Let(bindings, body) =>
      val bs = bindings map { case (v, t) => JsObject("var" -> toJSON(v), "value" -> toJSON(t)) }
      JsObject(
        "type" -> JsString("let"),
        "bindings" -> JsArray(bs.toVector),
        "body" -> toJSON(body)
      )

    case l: Literal =>
      JsObject(
        "type" -> JsString("literal"),
        "sort" -> toJSON(l.sort),
        "value" -> JsString(l.toString)
      )

    // PermLiteral is not actually a Literal. This case can actually be reached
    // and we map PermLiterals to normal literals.
    case p: PermLiteral =>
      JsObject(
        "type" -> JsString("literal"),
        "sort" -> toJSON(sorts.Perm),
        "value" -> JsString(p.toString)
      )

    case SeqRanged(p0, p1) => JsObject("type" -> JsString("seqRanged"), "lhs" -> toJSON(p0), "rhs" -> toJSON(p1))
    case SeqSingleton(p) => JsObject("type" -> JsString("seqSingleton"), "value" -> toJSON(p))
    case SeqUpdate(seq, index, value) => JsObject(
      "type" -> JsString("seqUpdate"),
      "seq" -> toJSON(seq),
      "index" -> toJSON(index),
      "value" -> toJSON(value)
    )

    case SingletonSet(p) => JsObject("type" -> JsString("singletonSet"), "value" -> toJSON(p))
    case SingletonMultiset(p) => JsObject("type" -> JsString("singletonMultiset"), "value" -> toJSON(p))

      // TODO: What about domains?

    case other => JsObject(
      "type" -> JsString("unstructrured"),
      "value" -> JsString(other.toString)
    )
  }
}
