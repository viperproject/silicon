/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon

import java.util.concurrent.ExecutionException
import viper.silver.verifier.{AbortedExceptionally => VprAbortedExceptionally, Failure => VprFailure, Success => VprSuccess, VerificationResult => VprVerificationResult}
import viper.silicon.interfaces.{Failure, Success, Unreachable, VerificationResult}

package object reporting {
  /** Extract the root exception that has been wrapped in one or more `ExecutionException`s. */
  def unwrapExecutionExceptions(exception: ExecutionException): Throwable = {
    var cause: Throwable = exception

    do {
      cause = cause.getCause
    } while (cause.isInstanceOf[ExecutionException])

    cause
  }

  def exceptionToViperError(exception: Exception): Either[Error, (Exception, VprFailure)] = {
    val cause: Throwable = exception match {
      case ee: ExecutionException => reporting.unwrapExecutionExceptions(ee)
      case _ => exception
    }

    cause match {
      case ex: SiliconException =>
        Right((ex, VprFailure(Seq(ex.asViperError))))
      case ex: Exception =>
        Right((ex, VprFailure(Seq(VprAbortedExceptionally(ex)))))
      case error: Error =>
        Left(error)
    }
  }

  val noClassDefFoundErrorMessage: String = (
      "A NoClassDefFoundError occurred (see below). As an attempt of solving this "
    + "problem, please delete the file 'silicon_classpath.txt' (should be in Silicon's "
    + "home directory), recompile Silicon (if possible) and then execute Silicon again.")

  def convertToViperResult(result: VerificationResult): VprVerificationResult = {
    result match {
      case Success() | Unreachable() => VprSuccess
      case Failure(message) => VprFailure(Seq(message))
    }
  }

  def convertToViperResults(results: Seq[VerificationResult]): Seq[VprVerificationResult] =
    results.map(convertToViperResult)

  def condenseToViperResult(results: Seq[VerificationResult]): VprVerificationResult = {
    results.map(convertToViperResult)
           .collect { case failure: VprFailure => failure.errors }
           .flatten match {
              case Seq() => VprSuccess
              case errors => VprFailure(errors)
            }
  }
}
