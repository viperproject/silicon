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
import viper.silicon.logger.{MemberSymbExLogger, NoopMemberSymbExLog}
import viper.silicon.state._
import viper.silicon.state.terms.{AxiomRewriter, TriggerGenerator}
import viper.silicon.supporters._
import viper.silicon.reporting.DefaultStateFormatter
import viper.silicon.rules.{DefaultStateConsolidator, LastRetryFailOnlyStateConsolidator, LastRetryStateConsolidator, MinimalRetryingStateConsolidator, MinimalStateConsolidator, MoreComplexExhaleStateConsolidator, RetryingFailOnlyStateConsolidator, RetryingStateConsolidator, StateConsolidationRules}
import viper.silicon.utils.Counter
import viper.silver.ast
import viper.silver.reporter.AnnotationWarning

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

  private var currentSymbExLog: Option[_ <: MemberSymbExLogger] = None
  override def symbExLog: MemberSymbExLogger = currentSymbExLog.getOrElse(NoopMemberSymbExLog)
  protected def symbExLog_=(logger: MemberSymbExLogger): Unit = { currentSymbExLog = Some(logger) }

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

  private lazy val defaultStateConsolidator: StateConsolidationRules = new DefaultStateConsolidator(config)
  private lazy val minimalStateConsolidator: StateConsolidationRules = new MinimalStateConsolidator
  private lazy val retryingStateConsolidator: StateConsolidationRules = new RetryingStateConsolidator(config)
  private lazy val retryingFailOnlyStateConsolidator: StateConsolidationRules = new RetryingFailOnlyStateConsolidator(config)
  private lazy val lastRetryStateConsolidator: StateConsolidationRules = new LastRetryStateConsolidator(config)
  private lazy val lastRetryFailOnlyStateConsolidator: StateConsolidationRules = new LastRetryFailOnlyStateConsolidator(config)
  private lazy val minimalRetryingStateConsolidator: StateConsolidationRules = new MinimalRetryingStateConsolidator(config)
  private lazy val moreComplexExhaleStateConsolidator: StateConsolidationRules = new MoreComplexExhaleStateConsolidator(config)

  override def stateConsolidator(s: State): StateConsolidationRules = {
    import StateConsolidationMode._

    val mode = s.currentMember match {
      case Some(member) =>
        member.info.getUniqueInfo[ast.AnnotationInfo] match {
          case Some(ai) if ai.values.contains("stateConsolidationMode") =>
            val modeAnnotation = ai.values("stateConsolidationMode")
            try {
              modeAnnotation match {
                case Seq("minimal") => Minimal
                case Seq("default") => Default
                case Seq("retrying") => Retrying
                case Seq("minimalRetrying") => MinimalRetrying
                case Seq("moreCompleteExhale") => MoreCompleteExhale
                case Seq("lastRetry") => LastRetry
                case Seq("retryingFailOnly") => RetryingFailOnly
                case Seq("lastRetryFailOnly") => LastRetryFailOnly
                case Seq(v) => StateConsolidationMode(v.toInt)
              }
            } catch {
              case _ =>
                reporter report AnnotationWarning(s"Member ${member.name} has invalid stateConsolidationMode annotation value. Annotation will be ignored.")
                config.stateConsolidationMode()
            }
          case _ => config.stateConsolidationMode()
        }
      case None => config.stateConsolidationMode()
    }

    mode match {
      case Minimal => minimalStateConsolidator
      case Default => defaultStateConsolidator
      case Retrying => retryingStateConsolidator
      case MinimalRetrying => minimalRetryingStateConsolidator
      case MoreCompleteExhale => moreComplexExhaleStateConsolidator
      case LastRetry => lastRetryStateConsolidator
      case RetryingFailOnly => retryingFailOnlyStateConsolidator
      case LastRetryFailOnly => lastRetryFailOnlyStateConsolidator
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
