/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package  viper.silicon.supporters.qps

import viper.silver.ast
import viper.silver.ast.{Predicate, Program}
import viper.silicon.Map
import viper.silicon.state.terms.{Var, sorts}
import viper.silicon.state.{Identifier, SymbolConverter, terms}
import viper.silver.components.StatefulComponent
import viper.silicon.supporters.SnapshotSupporter

class PredicateSnapGenerator(symbolConverter: SymbolConverter, snapshotSupporter: SnapshotSupporter)
    extends StatefulComponent {

  var snapMap: Map[Predicate, terms.Sort] = Map()
  var formalVarMap: Map[Predicate, Seq[terms.Var]] = Map()

  def setup(program:Program): Unit =
    program visit {
      case ast.PredicateAccess(_, predname) =>
        val predicate = program.findPredicate(predname)
        val sort = predicate -> predicate.body.map(snapshotSupporter.optimalSnapshotSort(_, program)._1).getOrElse(terms.sorts.Snap)
        val formalArgs:Seq[Var] = predicate.formalArgs.map(formalArg => Var(Identifier(formalArg.name), symbolConverter.toSort(formalArg.typ)))
        formalVarMap += predicate -> formalArgs
        snapMap += sort
    }

  def getSnap(predicate:Predicate): (terms.Sort, Boolean) =
    if (snapMap.contains(predicate)) {
      (snapMap(predicate), true)
    } else {
      (sorts.Snap, false)
    }

  /* Lifecycle */

  def start(): Unit = {}

  def reset(): Unit = {
    snapMap = Map.empty
    formalVarMap = Map.empty
  }

  def stop(): Unit = {}
}
