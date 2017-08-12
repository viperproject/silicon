/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.verifier

import java.util.concurrent._
import org.apache.commons.pool2.{BasePooledObjectFactory, ObjectPool, PoolUtils, PooledObject}
import org.apache.commons.pool2.impl.{DefaultPooledObject, GenericObjectPool, GenericObjectPoolConfig}
import viper.silicon.Config
import viper.silicon.interfaces.VerificationResult
import viper.silver.components.StatefulComponent
import viper.silicon.interfaces.decider.ProverLike
import viper.silicon.state.terms.{Decl, Term}

class VerificationPoolManager(master: MasterVerifier) extends StatefulComponent {
  private val numberOfSlaveVerifiers: Int = Verifier.config.numberOfParallelVerifiers()

  /*private*/ var slaveVerifiers: Seq[SlaveVerifier] = _
  /*private*/ var slaveVerifierExecutor: ExecutorService = _
  /*private*/ var slaveVerifierPool: ObjectPool[SlaveVerifier] = _

  /* private */ var runningVerificationTasks: ConcurrentHashMap[AnyRef, Boolean] = _

  private[verifier] object pooledVerifiers extends ProverLike {
    def emit(content: String): Unit = slaveVerifiers foreach (_.decider.prover.emit(content))
    def assume(term: Term): Unit = slaveVerifiers foreach (_.decider.prover.assume(term))
    def declare(decl: Decl): Unit =  slaveVerifiers foreach (_.decider.prover.declare(decl))
    def comment(content: String): Unit = slaveVerifiers foreach (_.decider.prover.comment(content))

    def saturate(data: Option[Config.Z3StateSaturationTimeout]): Unit =
      slaveVerifiers foreach (_.decider.prover.saturate(data))

    def saturate(timeout: Int, comment: String): Unit =
      slaveVerifiers foreach (_.decider.prover.saturate(timeout, comment))
  }

  /* Verifier pool management */

  private def setupSlaveVerifierPool(): Unit = {
    slaveVerifiers = Vector.empty
    runningVerificationTasks = new ConcurrentHashMap()

    val poolConfig: GenericObjectPoolConfig = new GenericObjectPoolConfig()
    poolConfig.setMaxTotal(numberOfSlaveVerifiers)
    poolConfig.setMaxIdle(numberOfSlaveVerifiers) /* Prevent pool from shutting down idle Z3 instances */
    poolConfig.setBlockWhenExhausted(true)

    val factory = PoolUtils.synchronizedPooledFactory(slaveVerifierPoolableObjectFactory)

    slaveVerifierPool =
    //    PoolUtils.synchronizedPool(
    new GenericObjectPool[SlaveVerifier](factory, poolConfig)
    //    )

    PoolUtils.prefill(slaveVerifierPool, poolConfig.getMaxTotal)
    //  Thread.sleep(2000)

    assert(slaveVerifiers.length == poolConfig.getMaxTotal)
    slaveVerifiers foreach (_.start())

    slaveVerifierExecutor = Executors.newFixedThreadPool(poolConfig.getMaxTotal)
//    slaveVerifierExecutor = Executors.newWorkStealingPool(poolConfig.getMaxTotal)
  }

  private def resetSlaveVerifierPool(): Unit = {
    slaveVerifiers foreach (_.reset())

    runningVerificationTasks.clear()
  }

  private def teardownSlaveVerifierPool(): Unit = {
    if (slaveVerifiers != null) {
      slaveVerifiers foreach (_.stop())

      slaveVerifierExecutor.shutdown()
      slaveVerifierExecutor.awaitTermination(10, TimeUnit.SECONDS)
    }

    if (slaveVerifierPool != null) {
      slaveVerifierPool.close()
    }
  }

  private object slaveVerifierPoolableObjectFactory extends BasePooledObjectFactory[SlaveVerifier] {
    def create(): SlaveVerifier = {
      val slave = new SlaveVerifier(master, master.nextUniqueVerifierId())
      slaveVerifiers = slave +: slaveVerifiers

      slave
    }

    def wrap(arg: SlaveVerifier): PooledObject[SlaveVerifier] = new DefaultPooledObject(arg)
  }

  /* Verification task management */

  private final class SlaveBorrowingVerificationTask(task: SlaveVerifier => Seq[VerificationResult])
      extends Callable[Seq[VerificationResult]] {

    def call(): Seq[VerificationResult] = {
      var slave: SlaveVerifier = null

      try {
        slave = slaveVerifierPool.borrowObject()

        task(slave)
      } finally {
        if (slave != null) {
          slaveVerifierPool.returnObject(slave)
        }
      }
    }
  }

  def queueVerificationTask(task: SlaveVerifier => Seq[VerificationResult])
                           : Future[Seq[VerificationResult]] = {

    slaveVerifierExecutor.submit(new SlaveBorrowingVerificationTask(task))
  }

  /* Lifetime */

  def start(): Unit = {
    setupSlaveVerifierPool()
  }

  def reset(): Unit = {
    resetSlaveVerifierPool()
  }

  def stop(): Unit = {
    teardownSlaveVerifierPool()
  }
}
