/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon

import java.util.concurrent.ExecutionException

package object reporting {
  /** Extract the root exception that has been wrapped in one or more `ExecutionException`s. */
  def getRootCause(exception: ExecutionException): Throwable = {
    var cause: Throwable = exception

    do {
      cause = cause.getCause
    } while (cause.isInstanceOf[ExecutionException])

    cause
  }
}
