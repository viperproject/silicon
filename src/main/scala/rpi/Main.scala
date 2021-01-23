package rpi

/**
  * The main object with the main method.
  */
object Main extends PrintRunner {
  /**
    * The base options for any kind of inference.
    */
  val baseOptions: Seq[String] = Seq.empty

  /**
    * The options for an inference with heuristics.
    */
  val heuristicsOptions: Seq[String] = baseOptions ++ Seq("--useHeuristics")

  /**
    * The options for an inference with annotations.
    */
  val annotationsOptions: Seq[String] = baseOptions ++ Seq("--useAnnotations")

  /**
    * The main method, i.e., the entry point of the inference.
    *
    * @param arguments The arguments to the inference.
    */
  def main(arguments: Array[String]): Unit = {
    run(arguments)
  }
}
