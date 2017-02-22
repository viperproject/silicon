/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.common

import java.io.{
    File => JFile,
    PrintWriter => JPrintWriter,
    BufferedWriter => JBufferedWriter,
    FileWriter => JFileWriter}
import java.nio.file.{Files, Paths}

import org.apache.commons.io.FilenameUtils

package object io {
  /**
   * Writes the `contents` to the given `file`. Existing content will be overwritten.
   *
   * @param contents The content to write.
   * @param file The file to which the content will be written.
   */
  def toFile(contents: String, file: JFile) {
    val sink = PrintWriter(file)

    sink.write(contents)
    sink.close()
  }

  /**
   * Creates a `java.io.PrintWriter` with `autoFlush` enabled that writes to the given `file`.
   * `File.mkdirs()` is called to ensure that the file path exists.
   *
   * @param file Is assumed to denote a file, not a directory.
   * @return The instantiated sink.
   */
  def PrintWriter(file: JFile, autoFlush: Boolean = true, append: Boolean = false): JPrintWriter = {
    val pf = file.getParentFile
    if (pf != null) pf.mkdirs()

    new JPrintWriter(new JBufferedWriter(new JFileWriter(file, append)), autoFlush)
  }

  def makeFilenameUnique(file: JFile,
                         targetDirectory: Option[JFile] = None,
                         newExtension: Option[String] = None)
                        : JFile = {

    targetDirectory.foreach(d => assert(d.isDirectory, s"Expected a directory, but found $d"))

    val fileStr = file.toString
    val directory = targetDirectory.getOrElse(FilenameUtils.getFullPath(fileStr)).toString
    val baseName = FilenameUtils.getBaseName(fileStr)
    val extension = newExtension.getOrElse(FilenameUtils.getExtension(fileStr))

    var counter: Long = 0
    var uniqueBaseName = baseName
    var uniqueFile = Paths.get(directory, s"$uniqueBaseName.$extension")

    /* Note: Theoretically, this loop might not terminate */
    while (Files.exists(uniqueFile)) {
      counter += 1
      uniqueBaseName = baseName + counter
      uniqueFile = Paths.get(directory, s"$uniqueBaseName.$extension")
    }

    uniqueFile.toFile
  }
}
