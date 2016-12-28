/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.verifier

import org.slf4s.Logging
import viper.silver.components.StatefulComponent
import viper.silicon._
import viper.silicon.decider.{DeciderProvider, TermToSMTLib2Converter}
import viper.silicon.state._
import viper.silicon.state.terms.AxiomRewriter
import viper.silicon.supporters._
import viper.silicon.supporters.qps._
import viper.silicon.reporting.{Bookkeeper, DefaultStateFormatter}
import viper.silicon.utils
import viper.silicon.verifier.BaseVerifier._

object BaseVerifier {
  type ST = MapBackedStore
  type H = ListBackedHeap
  type S = DefaultState[ST, H]
  type C = DefaultContext[H]
}

/** `uniqueId` is expected to meet the following requirements:
  *   1. unique across all instances of BaseVerifier
  *   2. usable in directory or file names
  *   3. usable in prover symbol names
  */
abstract class BaseVerifier(protected val config: Config,
                            protected val uniqueId: String)
    extends utils.NoOpStatefulComponent
       with DeciderProvider[ST, H, S]
       with DefaultEvaluator[ST, H, S]
       with DefaultProducer[ST, H, S]
       with DefaultConsumer[ST, H, S]
       with DefaultExecutor[ST, H, S]
       with ChunkSupporterProvider[ST, H, S]
       with DefaultBrancher[ST, H, S]
       with DefaultJoiner[ST, H, S]
       with DefaultLetHandler[ST, H, S, C]
       with MagicWandSupporter[ST, H, S]
       with HeuristicsSupporter[ST, H, S]
       with HeapCompressorProvider[ST, H, S, C]
       with QuantifiedChunkSupporterProvider[ST, H, S]
       with QuantifiedPredicateChunkSupporterProvider[ST, H, S]
       with Logging {

  protected implicit val manifestH: Manifest[H] = manifest[H]

  /*protected*/ val bookkeeper = new Bookkeeper(config, uniqueId)
  protected val stateFormatter = new DefaultStateFormatter[ST, H, S](config)
  protected val symbolConverter = new DefaultSymbolConvert()
  protected val termConverter = new TermToSMTLib2Converter(bookkeeper)
  protected val domainTranslator = new DefaultDomainsTranslator(symbolConverter)
  protected val stateFactory = new DefaultStateFactory()
  protected val identifierFactory = new DefaultIdentifierFactory(uniqueId)
  protected val axiomRewriter = new AxiomRewriter(new utils.Counter(), bookkeeper.logfiles(s"axiomRewriter"))
  protected val predSnapGenerator = new PredicateSnapGenerator(symbolConverter)

  private val statefulSubcomponents = List[StatefulComponent](
    bookkeeper,
    decider, identifierFactory,
    quantifiedChunkSupporter, quantifiedPredicateChunkSupporter )

  /* Lifetime */

  override def start() {
    super.start()
    statefulSubcomponents foreach (_.start())
  }

  override def reset() {
    super.reset()
    statefulSubcomponents foreach (_.reset())
  }

  override def stop() {
    super.stop()
    statefulSubcomponents foreach (_.stop())
  }
}
