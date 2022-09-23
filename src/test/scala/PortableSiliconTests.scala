// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.tests

import java.nio.file.Path

import org.scalatest.DoNotDiscover
import viper.silicon.{Silicon, SiliconFrontend}
import viper.silver.reporter.NoopReporter
import viper.silver.testing.{SilSuite, StatisticalTestSuite}
import viper.silver.verifier.Verifier


/** This test mechanism is intended for running non-default test suites,
  * in a portable way. Example run command:
  *
  * ```
  * Z3_EXE=z3.exe
  * sbt "test:runMain
  *      -DSILICONTESTS_TARGET=./target
  *      -DSILICONTESTS_WARMUP=./warmup
  *      -DSILICONTESTS_REPETITIONS=5
  *      -DSILICONTESTS_CSV=data.csv
  *      org.scalatest.tools.Runner
  *      -o -s
  *      viper.silicon.tests.PortableSiliconTests"
  * ```
  *
  * The command above will:
  * 1. Warm-up the JVM by verifying all .vpr files in ./warmup
  * 2. Measure time of 5 runs of each .vpr file in ./target
  * 3. Discard ("trim") the slowest and the fastest runs and compute
  *   - the mean
  *   - absolute and relative standard deviation
  *   - the best
  *   - the median
  *   - the worst
  *   run times of all these tests, and
  * 4. Print the timing info (per phase) into STDOUT, and write mean and standard deviation
  *    to file data.csv
  * 5. Create JAR files (e.g., target/scala-2.12/silicon_2.12-1.1-SNAPSHOT.jar,
  *                            target/scala-2.12/silicon_2.12-1.1-SNAPSHOT-tests.jar)
  *    that can be used to run tests with SBT without the need to distribute/ recompile
  *    the Viper sources. To run the test without recompiling the sources, these
  *    JAR files should be put into a directory test-location/lib/
  *    where test-location/ is the directory where you invoke SBT via:
  *    ```
  *    sbt "set trapExit := false" \
  *    "test:runMain org.scalatest.tools.Runner -o -s viper.silicon.tests.PortableSiliconTests"
  *    ```
  *    Note that this command takes the same JVM property arguments as used above.
  *
  * The warmup and the target must be disjoint (not in a sub-directory relation).
  *
  * The following JVM properties are available:
  *   - SILICONTESTS_TARGET = path/to/target/files/    // Mandatory
  *   - SILICONTESTS_WARMUP = path/to/warmup/files/    // Optional. If not specified, skip JVM warmup phase.
  *   - SILICONTESTS_REPETITIONS = n // Optional, defaults to 1. If less than 4, no "trimming" will happen.
  *   - SILICONTESTS_CSV = path/to/file.csv // Optional. If provided, mean & stddev are written to CSV file.
  *   - SILICONTESTS_RANDOMIZE_Z3 = bool // Optional, defaults to true. If true, passes --z3RandomizeSeeds to Silicon.
  */
@DoNotDiscover
class PortableSiliconTests extends SilSuite with StatisticalTestSuite {
  /** Following a hyphenation-based naming scheme is important for handling project-specific annotations.
    * See comment for [[viper.silver.testing.TestAnnotations.projectNameMatches()]].
    */
  override def name = "Silicon-Statistics"

  override val repetitionsPropertyName = "SILICONTESTS_REPETITIONS"
  override val warmupLocationPropertyName = "SILICONTESTS_WARMUP"
  override val targetLocationPropertyName = "SILICONTESTS_TARGET"
  override val csvFilePropertyName = "SILICONTESTS_CSV"
  override val inclusionFilePropertyName = "SILICONTESTS_INCL_FILE"
  val randomizePropertyName = "SILICONTESTS_RANDOMIZE_Z3"
  val timeoutPropertyName = "SILICONTESTS_TIMEOUT"

  val commandLineArguments: Seq[String] = Seq(
    "--disableCatchingExceptions",
    "--timeout", System.getProperty(timeoutPropertyName, "180") /* timeout in seconds */
  ) ++ (if (System.getProperty(randomizePropertyName, "false").toBoolean) Seq("--proverRandomizeSeeds") else Seq.empty)

  lazy val verifier: Silicon = {
    val args =
      commandLineArguments ++
        Silicon.optionsFromScalaTestConfigMap(prefixSpecificConfigMap.getOrElse("silicon", Map()))
    val reporter = NoopReporter
    val debugInfo = ("startedBy" -> "viper.silicon.SiliconTests") :: Nil
    val silicon = Silicon.fromPartialCommandLineArguments(args, reporter, debugInfo)

    silicon
  }

  override def frontend(verifier: Verifier, files: Seq[Path]): SiliconFrontend = {
    require(files.length == 1, "tests should consist of exactly one file")

    val fe = new SiliconFrontend(NoopReporter)//SiliconFrontendWithUnitTesting()
    fe.init(verifier)
    fe.reset(files.head)
    fe
  }
}
