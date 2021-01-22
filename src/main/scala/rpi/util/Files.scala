package rpi.util

import java.io.File

object Files {
  /**
    * Lists all files in the folder specified by the given path. If the path points to a file, a list containing that
    * file is returned.
    *
    * @param path The path.
    * @return The sequence of files.
    */
  def listFiles(path: File): Seq[File] =
    if (path.isDirectory)
      path
        .listFiles
        .toSeq
        .flatMap { child => listFiles(child) }
    else Seq(path)

}
