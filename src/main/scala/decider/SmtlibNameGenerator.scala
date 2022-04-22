// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.decider

import scala.util.matching.Regex

trait NameSanitizer {
  def firstCharacters: Regex
  def otherCharacters: Regex
  def substitutions: Map[Char, Char]
  def fallback: String
  def reservedNames: Set[String]
  def sanitize(name: String): String
}

abstract class AbstractNameSanitizer extends NameSanitizer {
  def sanitize(name: String): String = {
    assert(name.nonEmpty)

    val builder = new StringBuilder
    val first = name.head

    def handle(c: Char, pattern: Regex): Unit = {
      if (pattern.findFirstIn(c.toString).isDefined)
        builder.append(c)
      else
        builder.append(substitutions.getOrElse(c, fallback))
    }

    handle(first, firstCharacters)
    for (c <- name.tail) handle(c, otherCharacters)

    while (reservedNames.contains(builder.result())) {
      builder.append(fallback)
    }

    builder.result()
  }
}

class SmtlibNameSanitizer extends AbstractNameSanitizer {
  override val fallback = "_"

  override val substitutions = Map(
    '#' -> '%',
    //    "τ" -> "$tau",
    '[' -> '<',
    ']' -> '>',
  //    "::" -> ".",
    ':' -> '_',
    ',' -> '~',
    ' ' -> '_'
  )

  private val saveChars: String = fallback + "_$$@a-zA-Z" ++ substitutions.values

  val firstCharacters: Regex = s"[$saveChars]".r
  val otherCharacters: Regex = s"[0-9.$saveChars]".r

  val reservedNames: Set[String] = Set(
    /* SMT-LIB 2.6 - Predefined symbols */
    "Bool", "continued-execution", "error", "false", "immediate-exit", "incomplete", "logic",
    "memout", "sat", "success", "theory", "true", "unknown", "unsupported", "unsat",

    /* SMT-LIB 2.6 - Predefined keywords */
    "all-statistics", "assertion-stack-levels", "authors", "category", "chainable", "definition",
    "diagnostic-output-channel", "error-behavior", "extensions", "funs", "funs-description",
    "global-declarations", "interactive-mode", "language", "left-assoc", "license", "name", "named",
    "notes", "pattern", "print-success", "produce-assignments", "produce-models", "produce-proofs",
    "produce-unsat-assumptions", "produce-unsat-cores", "random-seed", "reason-unknown",
    "regular-output-channel", "reproducible-resource-limit", "right-assoc", "smt-lib-version",
    "sorts", "sorts-description", "source", "status", "theories", "values", "verbosity", "version",

    /* SMT-LIB 2.6 - Tokens - Reserved words - General */
    "!", "_", "as", "BINARY", "DECIMAL", "exists", "HEXADECIMAL", "forall", "let", "match",
    "NUMERAL", "par", "STRING",

    /* SMT-LIB 2.6 - Tokens - Reserved words - Command names */
    "assert", "check-sat", "check-sat-assuming", "declare-const",
    "declare-datatype", "declare-datatypes", "declare-fun", "declare-sort", "define-fun",
    "define-fun-rec", "define-sort", "echo", "exit", "get-assertions", "get-assignment", "get-info",
    "get-model", "get-option", "get-proof", "get-unsat-assumptions", "get-unsat-core", "get-value",
    "pop", "push", "reset", "reset-assertions", "set-info", "set-logic", "set-option",

    /* SMT-LIB 2.6 - Theories - Core */
    "Bool", "true", "false", "not", "and", "or", "xor", "ite", "implies", "iff", "distinct",
    "equiv",

    /* SMT-LIB 2.6 - Theories - Ints */
    "Int", "div", "mod", "abs",

    /* SMT-LIB 2.6 - Theories - Reals */
    "Real",

    /* SMT-LIB 2.6 - Theories - ArraysEx */
    "Array", "select", "store",

    /* SMT-LIB 2.6 - Theories - FixedSizeBitVectors */
    "BitVec", "concat", "extract", "bvnot", "bvneg", "bvand", "bvor", "bvadd", "bvmul", "bvudiv",
    "bvurem", "bvshl", "bvlshr", "bvult", "div", "rem", "bv2nat", "nat2bv",

    /* SMT-LIB 2.6 - Theories - Reals_Ints */
    "to_real", "to_int", "is_int",

    /* SMT-LIB 2.6 - Theories - Floating points */
    "to_real", "to_int", "is_int",

    /* TODO: Separate SMT-LIB from Z3 keywords by moving the latter to a subclass of
     *       SmtlibNameGenerator
     *
     * TODO: Add keywords from Z3's support for tactics, fix-points and optimisations (objective
     *       functions)
     */

    /* Z3 strings, sequences and regular expressions */
    "String",
    "str.len", "str.substr", "str.indexof", "str.indexof", "str.at", "str.contains", "str.prefixof",
    "str.suffixof", "str.replace", "str.to.int", "int.to.str",
    "Seq",
    "seq.unit", "seq.empty", "seq.len", "seq.extract", "seq.indexof", "seq.at", "seq.contains",
    "seq.prefixof", "seq.suffixof", "seq.replace",
    "RegEx",
    "str.to.re", "str.in.re", "re.allchar", "re.nostr", "re.range", "re.opt", "re.loop", "re.union",
    "re.inter", "seq.to.re", "seq.in.re", "re.all", "re.empty",

    /* Other reserved words (Z3 specific?) */
    "min", "List", "const",

    /* cvc5 - Transcendental operators, see https://github.com/cvc5/cvc5/blob/main/src/parser/smt2/smt2.cpp */
    "exp", "sin", "cos", "tan", "csc", "sec", "cot", "arcsin", "arccos", "arctan", "arccsc", "arcsec", "arccot", "sqrt",

    /* cvc5 - Commands, see https://github.com/cvc5/cvc5/blob/main/docs/ext/smtliblexer.py */
    "block-model", "block-model-values", "declare-codatatypes",
    "define-const", "define-funs-rec", "get-abduct", "get-abduct-next",
    "get-interpolant", "get-qe", "get-qe-disjunct", "assume", "check-synth",
    "constraint", "declare-var", "inv-constraint", "synth-fun", "synth-inv",
    "declare-pool",

    /* cvc5 - Sorts, see https://github.com/cvc5/cvc5/blob/main/docs/ext/smtliblexer.py */
    "Bag", "FloatingPoint", "Float[0-9]+", "RegLan", "RoundingMode", "Set", "Tuple",

    /* cvc5 - Operators, see https://github.com/cvc5/cvc5/blob/main/docs/ext/smtliblexer.py */
    "repeat", "zero_extend", "sign_extend", "rotate_left", "rotate_right",
    "bvnand", "bvnor", "bvxor", "bvxnor", "bvcomp", "bvsub", "bvsdiv",
    "bvsrem", "bvsmod", "bvashr", "bvule", "bvugt", "bvuge", "bvslt", "bvsle",
    "bvsgt", "bvsge", "tuple", "tuple.project", "tuple.select",
    "tuple.update", "RNE", "RNA", "RTP", "RTN", "RTZ", "fp", "NaN", "fp.abs",
    "fp.neg", "fp.add", "fp.sub", "fp.mul", "fp.div", "fp.fma", "fp.sqrt",
    "fp.rem", "fp.roundToIntegral", "fp.min", "fp.max", "fp.leq", "fp.lt",
    "fp.geq", "fp.gt", "fp.eq", "fp.isNormal", "fp.isSubnormal", "fp.isZero",
    "fp.isInfinite", "fp.isNaN", "fp.isNegative", "fp.isPositive", "to_fp",
    "to_fp_unsigned", "fp.to_ubv", "fp.to_sbv", "fp.to_real", "+oo", "-oo",
    "+zero", "-zero", "divisible", "iand", "int2bv", "sep.emp", "pto", "sep",
    "wand", "sep.nil", "set.union", "set.minus", "set.member", "set.subset",
    "set.empty", "set.singleton", "set.card", "set.insert", "set.complement",
    "set.universe", "rel.transpose", "rel.tclosure", "rel.join",
    "rel.product", "set.inter", "char", "str.++", "str.<", "str.<=",
    "str.to_re", "str.in_re", "re.none", "re.++", "re.*", "str.<=",
    "str.replace_all", "str.replace_re", "str.replace_re_all", "re.comp",
    "re.diff", "re.+", "re.^", "str.is_digit", "str.to_code", "str.from_code",
    "str.to_int", "str.from_int", "seq.++", "seq.update", "seq.rev",
    "seq.replace_all", "seq.nth", "witness"
  )
}
