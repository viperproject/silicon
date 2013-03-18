package semper
package silicon
package common

import java.io.{
  File => JFile,
  PrintWriter => JPrintWriter,
  BufferedWriter => JBufferedWriter,
  FileWriter => JFileWriter}

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
  def PrintWriter(file: JFile): JPrintWriter = {
    file.getParentFile.mkdirs()

    new JPrintWriter(new JBufferedWriter(new JFileWriter(file)), true)
  }
}
