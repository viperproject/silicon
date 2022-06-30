// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.verifier

import com.typesafe.scalalogging.Logger
import org.slf4j.LoggerFactory
import viper.silicon.Config.StateConsolidationMode
import viper.silver.components.StatefulComponent
import viper.silicon.{utils, _}
import viper.silicon.decider.{DefaultDeciderProvider, TermToSMTLib2Converter}
import viper.silicon.state._
import viper.silicon.state.terms.{AxiomRewriter, TriggerGenerator}
import viper.silicon.supporters._
import viper.silicon.reporting.DefaultStateFormatter
import viper.silicon.rules.{DefaultStateConsolidator, MinimalRetryingStateConsolidator, MinimalStateConsolidator, MoreComplexExhaleStateConsolidator, RetryingStateConsolidator, StateConsolidationRules}
import viper.silicon.utils.Counter

import scala.collection.mutable

/** `uniqueId` is expected to meet the following requirements:
  *   1. unique across all instances of BaseVerifier
  *   2. usable in directory or file names
  *   3. usable in prover symbol names
  */
abstract class BaseVerifier(val config: Config,
                            val uniqueId: String)
    extends utils.NoOpStatefulComponent
       with Verifier
       with DefaultDeciderProvider {

  val logger: Logger =
    Logger(LoggerFactory.getLogger(s"${this.getClass.getName}-$uniqueId"))

  private val counters = mutable.Map[AnyRef, Counter]()

  def counter(id: AnyRef): Counter = {
    counters.getOrElseUpdate(id, new Counter())
  }

//  /*protected*/ val bookkeeper = new Bookkeeper(config, uniqueId)
  val stateFormatter = new DefaultStateFormatter()
  val symbolConverter = new DefaultSymbolConverter()
  val termConverter = new TermToSMTLib2Converter(/*bookkeeper*/)
  val domainTranslator = new DefaultDomainsTranslator()
  val identifierFactory = new DefaultIdentifierFactory(uniqueId)
  val triggerGenerator = new TriggerGenerator()
  val axiomRewriter = new AxiomRewriter(new utils.Counter()/*, bookkeeper.logfiles(s"axiomRewriter")*/, triggerGenerator)
  val quantifierSupporter = new DefaultQuantifierSupporter(triggerGenerator)
  val snapshotSupporter = new DefaultSnapshotSupporter(symbolConverter)

  val stateConsolidator: StateConsolidationRules = {
    import StateConsolidationMode._

    config.stateConsolidationMode() match {
      case Minimal => new MinimalStateConsolidator
      case Default => new DefaultStateConsolidator(config)
      case Retrying => new RetryingStateConsolidator(config)
      case MinimalRetrying => new MinimalRetryingStateConsolidator(config)
      case MoreCompleteExhale => new MoreComplexExhaleStateConsolidator(config)
    }
  }

  private val statefulSubcomponents = List[StatefulComponent](
//    bookkeeper,
    decider,
    termConverter,
    identifierFactory)

  /* Lifetime */

  override def start(): Unit = {
    super.start()
    statefulSubcomponents foreach (_.start())
  }

  override def reset(): Unit = {
    super.reset()
    statefulSubcomponents foreach (_.reset())
    errorsReportedSoFar.set(0)
    counters.clear()
  }

  override def stop(): Unit = {
    super.stop()
    statefulSubcomponents foreach (_.stop())
  }
}
