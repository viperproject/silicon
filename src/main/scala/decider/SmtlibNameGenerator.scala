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
  def sanitize(name: String) = {
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

  val firstCharacters = s"[$saveChars]".r
  val otherCharacters = s"[0-9.$saveChars]".r

  val reservedNames: Set[String] = Set(
    /* SMTLIB 2.5 - Reserved words - General */
    "!", "_", "as", "BINARY", "DECIMAL", "exists", "HEXADECIMAL", "forall", "let", "NUMERAL", "par",
    "STRING",
    /* SMTLIB 2.5 - Reserved words - Command names */
    "assert", "check-sat", "check-sat-assuming", "declare-const", "declare-fun",
    "declare-sort", "define-fun", "define-fun-rec", "define-sort", "echo", "exit", "get-assertions",
    "get-assignment", "get-info", "get-model", "get-option", "get-proof", "get-unsat-assumptions",
    "get-unsat-core", "get-value", "pop", "push", "reset", "reset-assertions", "set-info", "set-logic",
    "set-option",
    /* SMTLIB 2.5 - Theory Bool */
    "Bool", "true", "false", "not", "and", "or", "xor", "ite", "implies", "iff", "distinct",
    /* SMTLIB 2.5 - Theory Int */
    "Int", "div", "mod", "abs",
    /* SMTLIB 2.5 - Theory Reals */
    "Real",
    /* SMTLIB 2.5 - Theory ArraysEx */
    "Array", "select", "store",
    /* SMTLIB 2.5 - Theory FixedSizeBitVectors */
    "BitVec", "concat", "extract", "bvnot", "bvneg", "bvand", "bvor", "bvadd", "bvmul", "bvudiv",
    "bvurem", "bvshl", "bvlshr", "bvult",
    /* SMTLIB 2.5 - Theory Reals_Ints */
    "to_real", "to_int", "is_int",
    /* Other reserved words (Z3 specific?) */
    "min", "List", "const"
  )
}
