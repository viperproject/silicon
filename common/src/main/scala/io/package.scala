package semper
package silicon
package common

import java.io.File

package object io {
  def toFile(contents: String, file: File) {
    val sink =
      new java.io.PrintWriter(
        new java.io.BufferedWriter(
          new java.io.FileWriter(file)),
        true)

    sink.write(contents)
    sink.close()
  }
}