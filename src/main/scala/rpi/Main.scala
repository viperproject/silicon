package rpi

/**
  * The main object with the main method.
  */
object Main extends PrintRunner {
  /**
    * The main method, i.e., the entry point of the inference.
    *
    * @param arguments The arguments to the inference.
    */
  def main(arguments: Array[String]): Unit = {
    run(arguments)
  }
}
