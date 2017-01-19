/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.verifier

import java.util.concurrent._

import org.apache.commons.pool2.{BasePooledObjectFactory, ObjectPool, PoolUtils, PooledObject}
import org.apache.commons.pool2.impl.{DefaultPooledObject, GenericObjectPool, GenericObjectPoolConfig}
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
    slaveVerifiers foreach (_.stop())

    slaveVerifierExecutor.shutdown()
    slaveVerifierExecutor.awaitTermination(10, TimeUnit.SECONDS)

    slaveVerifierPool.close()
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
//        println(s"[${Thread.currentThread().getId}]")
//        println(s"  ###### Starting slave verification task")
//        println(s"  getNumActive = ${slaveVerifierPool.getNumActive}")
//        println(s"  getNumIdle = ${slaveVerifierPool.getNumIdle}")

        slave = slaveVerifierPool.borrowObject()
//        println(s"${Thread.currentThread().getId} BORROWS ${slave.uniqueId}")

//        println(s"  Borrowed slave = ${slave.uniqueId}")

        val r = task(slave)

//        println(s"[${Thread.currentThread().getId} | ${slave.uniqueId}]")
//        println(s"  ###### Done with slave verification task")

        r
      } finally {
        if (slave != null) {
//          println(s"${Thread.currentThread().getId} RETURNS ${slave.uniqueId}")
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

//class CustomFutureReturningExecutor(numberOfThreads: Int)
//    /* The initialisation of the ThreadPoolExecutor corresponds to OpenJDK-8's implementation of
//     * java.util.concurrent.Executors.newFixedThreadPool
//     * See http://grepcode.com/file/repository.grepcode.com/java/root/jdk/openjdk/8u40-b25/java/util/concurrent/Executors.java
//     */
//    extends ThreadPoolExecutor(numberOfThreads,
//                               numberOfThreads,
//                               0L,
//                               TimeUnit.MILLISECONDS,
//                               new LinkedBlockingQueue[Runnable]()) {
//
//  override protected def newTaskFor[T](runnable: Runnable, default: T): RunnableFuture = ???
//
//  override protected def newTaskFor[T](callable: Callable[T]): RunnableFuture = {
////    if (callable instanceof IdentifiableCallable) {
////      return ((IdentifiableCallable) callable).newTask();
////    } else {
////      return super.newTaskFor(callable); // A regular Callable, delegate to parent
////    }
//  ???}
//}
//
//class QueryableFutureTask[T](callable: Callable[T]) extends FutureTask(callable) {
//
//}
