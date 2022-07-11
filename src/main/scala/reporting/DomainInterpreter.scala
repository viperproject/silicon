// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package viper.silicon.reporting

import viper.silicon
import viper.silicon.state.terms._
import viper.silicon.state.Identifier

/**
  * the most Generic form of interpreter
  *  @param	E : input type
  *  @param I : info object type
  *  @param	T : result type
  */
trait AbstractInterpreter[E, I, T] { 
  def interpret(entry: E, info: I): T
}
trait ModelInterpreter[T, I] extends AbstractInterpreter[ExtractedModelEntry, I, T]
trait DomainInterpreter[T, I] extends AbstractInterpreter[DomainValueEntry, I, T]

case class IdentityInterpreter() extends ModelInterpreter[ExtractedModelEntry, Any] {
  def interpret(entry: ExtractedModelEntry, anything: Any): ExtractedModelEntry = entry
}

/**
  * Simple domain interpreter resolves entries in domains recursively otherwise it just returns the value of the entry
  * does not resolve domain values stored in sequences or Refs
  * @param c Converter that has all necessary infos about the counterexample domains
  */
case class GenericDomainInterpreter(c: Converter) extends ModelInterpreter[ExtractedModelEntry, Seq[ExtractedModelEntry]] {
  private val domains: Seq[DomainEntry] = c.domains
  private val functions: Seq[ExtractedFunction] = c.nonDomainFunctions
  def interpret(entry: ExtractedModelEntry, visited: Seq[ExtractedModelEntry]): ExtractedModelEntry = {
    if (visited.contains(entry)) entry
    else entry match {
      case DomainValueEntry(dom, v) =>
        val relevantDomain = domains.filter(x => x.valueName == dom)
        val domainFunctions = relevantDomain.flatMap(_.functions)
        val allFunctions = functions ++ domainFunctions
        val relevantFunctions = allFunctions.filter(x => x.argtypes.length == 1 && x.argtypes.head == sorts.UserSort(Identifier(dom)))
        val info = silicon.toMap(relevantFunctions.map(fn => (fn,
          fn(Seq(entry)) match {
            case Right(e) => e match {
              case d: DomainValueEntry => interpret(d, entry +: visited)
              case x => interpret(x, entry +: visited)
            }
            case _ => OtherEntry(s"${fn.fname}","not been able to resolve function")
          })))
        ExtendedDomainValueEntry(DomainValueEntry(dom, v), info)
      case e: VarEntry => interpret(c.extractVal(e), e +: visited)
      case r: RefEntry => RefEntry(r.name, r.fields.map {
        // interpret each field entry:
        case (fieldName, (entry, optPerm)) => (fieldName, (interpret(entry, r +: visited), optPerm))
      })
      case _ => entry
    }
  }
}
