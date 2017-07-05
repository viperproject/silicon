/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.common

import java.util.concurrent.{Callable, Future, TimeUnit}
import scala.language.implicitConversions

package object concurrency {
  class SynchronousFuture[T](callable: Callable[T]) extends Future[T] {
    private var result: Option[T] = None

    val isCancelled = false

    def isDone = result.isDefined

    def get(): T = {
      result match {
        case Some(t) => t
        case None =>
          val t = callable.call()
          result = Some(t)
          t
      }
    }

    def get(timeout: Long, unit: TimeUnit) = ???

    def cancel(mayInterruptIfRunning: Boolean) = ???
  }

  implicit def functionToCallable[R](f: => R): Callable[R] = new Callable[R]{
    def call: R = f
  }
}
