/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.state

import viper.silver.components.StatefulComponent
import viper.silicon.decider.NameSanitizer
import viper.silicon.utils.Counter

//trait Namespace {
//  def id: Int
//  def name: String
//}
//
//trait NamespaceFactory {
//  def fresh(name: String): Namespace
//}
//
//case class DefaultNameSpace(id: Int, name: String) extends Namespace
//
//class DefaultNamespaceFactory extends NamespaceFactory with StatefulComponent {
//  private val ids: Counter = new Counter
//
//  def fresh(name: String): Namespace = DefaultNameSpace(ids.next(), name)
//
//  def start(): Unit = {}
//  def reset(): Unit = { ids.reset() }
//  def stop(): Unit = {}
//}

//trait Identifier {
//  def name: String
////  def namespace: Namespace
//}

case class Identifier(name: String/*, namespace: Namespace*/) extends AnyVal {
  override def toString = name
}

trait IdentifierFactory {
  def separator: String
  def fresh(name: String/*, namespace: Namespace*/): Identifier
//  def fresh(name: String)(implicit namespace: Namespace) = fresh(name, namespace)
}

class DefaultIdentifierFactory/*(nameSanitizer: NameSanitizer)*/
    extends IdentifierFactory
       with StatefulComponent {

  private val ids: Counter = new Counter

  val separator = "@"

  def fresh(name: String/*, namespace: Namespace*/): Identifier = {
//    val sanitizedName = nameSanitizer.sanitize(name + separator)
//    val freshName = sanitizedName + ids.next()
    val freshName = s"$name$separator${ids.next()}"

    Identifier(freshName/*, namespace*/)
  }

  def start(): Unit = {}
  def reset(): Unit = { ids.reset() }
  def stop(): Unit = {}
}
