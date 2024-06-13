// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.axiomprofilerinfo

/** The axiom profiler info object is responsible for gathering data to export for the Axiom Profiler.
  * The data is exported in the form of a JSON file.
  * The JSON file should have 3 fields:
  * 1. "rules" - The rewriting rules for the Axiom Profiler to pretty print expressions.
  * 2. "quantifiers" - A list of quantifiers, each of them having the following fields:
  *    * "name" - The name of the quantifier.
  *    * "pos" - The line of code this quantifier is written in.
  * 3. "checks" - A list of checks, each of them being a string that describes what was the purpose of the check.
  */

import scala.collection.mutable.ArrayBuffer
import spray.json.{JsArray, JsNumber, JsObject, JsString}

object AxiomProfilerInfo {
  val rules = ArrayBuffer[String]()
  val quantifiers = ArrayBuffer[Map[String, Any]]()
  val checks = ArrayBuffer[String]()

  def addRule(rule: String): Unit = {
    rules += rule
  }

  def addQuantifier(name: String, pos: Int): Unit = {
    quantifiers += Map("name" -> name, "pos" -> pos)
  }

  def addCheck(check: String): Unit = {
    checks += check
  }

  def exportToFile(fileName: String): Unit = {
    import java.io._
    val pw = new PrintWriter(new File(fileName))
    pw.write(JsObject(
      "rules" -> JsArray(rules.map(JsString(_)).toList),
      "quantifiers" -> JsArray(quantifiers.map(q => JsObject(
        "name" -> JsString(q("name").asInstanceOf[String]),
        "pos" -> JsNumber(q("pos").asInstanceOf[Int])
      )).toList),
      "checks" -> JsArray(checks.map(JsString(_)).toList)
    ).prettyPrint)
    pw.close()
  }

}
