// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

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
  /*private*/ var slaveVerifierExecutor: ForkJoinPool = _
  /*private*/ var slaveVerifierPool: ObjectPool[SlaveVerifier] = _

  ///* private */ var runningVerificationTasks: ConcurrentHashMap[AnyRef, Boolean] = _

  private[verifier] object pooledVerifiers extends ProverLike {
    def emit(content: String): Unit = slaveVerifiers foreach (_.decider.prover.emit(content))
    override def emit(contents: Iterable[String]): Unit = slaveVerifiers foreach (_.decider.prover.emit(contents))
    def assume(term: Term): Unit = slaveVerifiers foreach (_.decider.prover.assume(term))
    def declare(decl: Decl): Unit =  slaveVerifiers foreach (_.decider.prover.declare(decl))
    def comment(content: String): Unit = slaveVerifiers foreach (_.decider.prover.comment(content))

    def saturate(data: Option[Config.ProverStateSaturationTimeout]): Unit =
      slaveVerifiers foreach (_.decider.prover.saturate(data))

    def saturate(timeout: Int, comment: String): Unit =
      slaveVerifiers foreach (_.decider.prover.saturate(timeout, comment))

    override def emitSettings(contents: Iterable[String]): Unit =
      slaveVerifiers foreach (_.decider.prover.emitSettings(contents))
  }

  /* Verifier pool management */

  private def setupSlaveVerifierPool(): Unit = {
    slaveVerifiers = Vector.empty
    //runningVerificationTasks = new ConcurrentHashMap()

    val poolConfig: GenericObjectPoolConfig[SlaveVerifier] = new GenericObjectPoolConfig()
    poolConfig.setMaxTotal(numberOfSlaveVerifiers)
    poolConfig.setMaxIdle(numberOfSlaveVerifiers) /* Prevent pool from shutting down idle prover instances */
    poolConfig.setBlockWhenExhausted(true)

    val factory = PoolUtils.synchronizedPooledFactory(slaveVerifierPoolableObjectFactory)

    slaveVerifierPool =
    //    PoolUtils.synchronizedPool(
    new GenericObjectPool[SlaveVerifier](factory, poolConfig)
    //    )

    slaveVerifierPool.addObjects(poolConfig.getMaxTotal)
    //  Thread.sleep(2000)

    assert(slaveVerifiers.length == poolConfig.getMaxTotal)
    slaveVerifiers foreach (_.start())

    //System.setProperty("java.util.concurrent.ForkJoinPool.common.maximumSpares", "0")
    slaveVerifierExecutor = new ForkJoinPool(poolConfig.getMaxTotal, new SlaveBorrowingForkJoinThreadFactory(), null, false)
    //slaveVerifierExecutor = Executors.newFixedThreadPool(poolConfig.getMaxTotal)
//    slaveVerifierExecutor = Executors.newWorkStealingPool(poolConfig.getMaxTotal)
  }

  private def resetSlaveVerifierPool(): Unit = {
    slaveVerifiers foreach (_.reset())

    //runningVerificationTasks.clear()
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
      val slave = new SlaveVerifier(master, master.nextUniqueVerifierId(), master.reporter)
      slaveVerifiers = slave +: slaveVerifiers

      slave
    }

    def wrap(arg: SlaveVerifier): PooledObject[SlaveVerifier] = new DefaultPooledObject(arg)
  }

  /* Verification task management */



  def queueVerificationTask(task: SlaveVerifier => Seq[VerificationResult])
                           : Future[Seq[VerificationResult]] = {
    val thread = Thread.currentThread()
    if (thread.isInstanceOf[SlaveBorrowingForkJoinWorkerThread]){
      new SlaveAwareForkJoinTask(task).fork
    }else{
      slaveVerifierExecutor.submit(new SlaveAwareForkJoinTask(task))
    }
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

  // new

  class SlaveBorrowingForkJoinThreadFactory extends ForkJoinPool.ForkJoinWorkerThreadFactory {
    override def newThread(forkJoinPool: ForkJoinPool): ForkJoinWorkerThread = {
      println("creating new thread")
      new SlaveBorrowingForkJoinWorkerThread(forkJoinPool)
    }
  }

  class SlaveBorrowingForkJoinWorkerThread(pool: ForkJoinPool) extends ForkJoinWorkerThread(pool) {
    var slave: SlaveVerifier = null

    override def onStart(): Unit = {
      println("starting new thread, trying to borrow " + this)
      slave = slaveVerifierPool.borrowObject()
      println("succeeded in borrowing " + this)
    }

    override def onTermination(exception: Throwable): Unit = {
      if (slave != null) {
        slaveVerifierPool.returnObject(slave)
      }
    }

  }


  class SlaveAwareForkJoinTask(task: SlaveVerifier => Seq[VerificationResult])
  //extends Callable[Seq[VerificationResult]] {
    extends RecursiveTask[Seq[VerificationResult]]{

    override def compute(): Seq[VerificationResult] = {
      //println("starting new task")
      val worker = Thread.currentThread().asInstanceOf[SlaveBorrowingForkJoinWorkerThread]
      val slave = worker.slave
      task(slave)
    }
  }
}


