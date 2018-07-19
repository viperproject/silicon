/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

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

    while (reservedNames.contains(builder.result)) {
      builder.append(fallback)
    }

    builder.result
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
    "min", "List", "const"
  )
}
