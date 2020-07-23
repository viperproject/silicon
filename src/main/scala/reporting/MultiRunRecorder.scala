// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.reporting

import java.io.{File, PrintWriter}

import scala.collection.mutable
import scala.reflect.ClassTag
import viper.silicon.Config
import viper.silicon.utils.notNothing.NotNothing
import viper.silicon.verifier.Verifier
import viper.silver.components.StatefulComponent

/* WARNING: The recording functionality provided by this file is *not thread-safe*!
 * It is advised to run Silicon with --numberOfParallelVerifiers 1 when using recorders.
 *
 * NOTE: Running the full test suite, i.e. `sbt> test`, runs multiple unit tests, and each of these runs
 * is likely to overwrite the previous recordings. If you're interested in recording data from the core test
 * suite (i.e. all Viper test files), the run `sbt> testOnly viper.silicon.tests.SiliconTests`.
 */

/* WARNING: Not thread-safe!
 *
 * TODO: Investigate if it is possible to base this class on a logging framework (e.g. slf4j) or a Viper reporter
 *
 * TODO: Investigate if the recorders can be unified with the loggers that are used if command-line
 *       option -L<logger> is provided
 */
trait MultiRunRecorder extends StatefulComponent {
  private var lastSeenSource: Either[_, Option[String]] = Left(()) /* Left() means we haven't seen a source yet */

  def source: Option[String]

  protected def detectSourceChange(): Boolean = {
    val previousSource = lastSeenSource.getOrElse(None)
    val currentSource = source
    val changed = previousSource != currentSource

    if (changed) {
      lastSeenSource = Right(currentSource)

      onSourceChanged(previousSource, currentSource)
    }

    changed
  }

  protected def onSourceChanged(previousSource: Option[String], currentSource: Option[String]): Unit

  def start() { /* nothing to do */ }
  def reset() { /* nothing to do */ }
  def stop() { /* nothing to do */ }
}

abstract class PrintWriterBasedMultiRunRecorder extends MultiRunRecorder {
  def sink: PrintWriter

  protected def formatNewSource(newSource: Option[String]): String = {
    val sep = "-" * 10

    newSource match {
      case Some(s) => s"\n$sep $s $sep\n"
      case None => s"\n$sep New unnamed source $sep\n"
    }
  }

  override def reset(): Unit = {
    sink.flush()

    super.reset()
  }
}

abstract class BufferingPrintWriterBasedMultiRunRecorder extends PrintWriterBasedMultiRunRecorder {
  protected def writeAndClearRecordedData(): Unit

  protected def onSourceChanged(previousSource: Option[String], currentSource: Option[String]): Unit = {
    writeAndClearRecordedData()

    sink.println(formatNewSource(currentSource))
  }

  override def stop(): Unit = {
    writeAndClearRecordedData()

    super.stop()
  }
}

object MultiRunRecorders extends StatefulComponent {
  private val recorders = mutable.HashMap.empty[String, MultiRunRecorder]
  private val sinks = mutable.ArrayBuffer.empty[PrintWriter]

  protected def config: Config = Verifier.config
  protected def source: Option[String] = Verifier.inputFile.map(_.toString)

  protected def sink(name: String): PrintWriter = {
    val writer =
      viper.silver.utility.Common.PrintWriter(
        new File(config.tempDirectory(), s"$name.log"), false)

    sinks += writer

    writer
  }

  def get[R <: MultiRunRecorder : NotNothing : ClassTag](name: String): R = {
    val recorder =
      recorders.getOrElseUpdate(name, {
        val sinkArgumentClass = classOf[PrintWriter]
        val sourceProviderArgumentClass = classOf[() => Option[String]]

        val runtimeClassOfR = implicitly[ClassTag[R]].runtimeClass
        val constructorOfR = runtimeClassOfR.getDeclaredConstructor(sinkArgumentClass, sourceProviderArgumentClass)

        constructorOfR.newInstance(sink(name), () => source).asInstanceOf[R]
      })

    recorder.asInstanceOf[R]
  }

  def start(): Unit = {
    assert(recorders.isEmpty)
    assert(sinks.isEmpty)
  }

  def reset() {
    recorders.valuesIterator.foreach(_.reset())
    sinks.foreach(_.flush())
  }

  def stop() {
    recorders.valuesIterator.foreach(_.stop())
    sinks.foreach(_.close())

    recorders.clear()
    sinks.clear()
  }
}