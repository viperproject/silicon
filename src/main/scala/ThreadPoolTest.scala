/*
import java.util.concurrent.Executors

import viper.silicon.{SiliconRunner, SiliconRunnerInstance}
import viper.silver.logger.ViperStdOutLogger

object ManySilicons {
  val noInstances = 8

  def main(args: Array[String]): Unit = {
    // gotta do this first, otherwise differrent threads race for it.
    val ummm = ViperStdOutLogger("SiliconFrontend", "INFO").get
    val argMap = Map(
      0 -> "/viper/new/silicon/silver/src/test/resources/examples/binary-search/binary-search-array.vpr",
      1 -> "/viper/new/silicon/silver/src/test/resources/quantifiedcombinations/injectivity_on_inhale.vpr",
      2 -> "/viper/new/silicon/silver/src/test/resources/adt/example_5.vpr",
      3 -> "/viper/new/silicon/silver/src/test/resources/adt/example_3.vpr",
      4 -> "/viper/new/silicon/silver/src/test/resources/examples/binary-search/binary-search-array.vpr",
      5 -> "/viper/new/silicon/silver/src/test/resources/wands/examples_new_syntax/ListIterator.vpr",
      6 -> "/viper/new/silicon/silver/src/test/resources/wands/examples_paper/tree_delete_min.vpr",
      7 -> "/viper/new/silicon/silver/src/test/resources/quantifiedcombinations/multiple_quantifiers.vpr")

    for (i <- 0 until 100){
      val pool = Executors.newFixedThreadPool(noInstances)
      def runnable(i: Int): Runnable = () => {
        Thread.sleep((Math.random() * 5000).toLong)
        (new SiliconRunnerInstance).runMain(Array(argMap(i)))
      }
      val futures = (0 until noInstances).map(i => pool.submit(runnable(i)))
      val results = futures.map(_.get())
      println(results)
      pool.shutdown()
    }
  }
}*/