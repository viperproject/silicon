// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2026 ETH Zurich.

package viper.silicon.tests

import java.io.File

import org.scalatest.DoNotDiscover

/** A small benchmark that can be run with `sbt benchmark`, useful to check performance
  * changes for a PR. It's not a rigorous performance test, more a sanity check. Results can
  * be compared using utils/scripts/compare_benchmarks.py.
  *
  * Benchmarks every file in the target directory (default [[SiliconBenchmark.DefaultTarget]]),
  * plus some Silver/Silicon test cases listed in [[SiliconBenchmark.ExtraFiles]].
  * The benchmark should have good coverage of Silicon features, but take less than 30min
  * for 10 reps (don't be afraid to remove or replace benchmark cases).
  *
  * All defaults can be overridden with the same JVM properties as [[PortableSiliconTests]],
  * e.g. `sbt -DSILICONTESTS_REPETITIONS=10 -DSILICONTESTS_CSV=mine.csv benchmark`.
  */
@DoNotDiscover
class SiliconBenchmark extends PortableSiliconTests {
  import SiliconBenchmark._

  override def name = "Silicon-Benchmarks"

  private def property(key: String): Option[String] =
    Option(System.getProperty(key)).map(_.trim).filter(_.nonEmpty)

  override protected def targetDirName: String =
    property(targetLocationPropertyName).getOrElse(DefaultTarget)

  override protected def warmupDirName: Option[String] =
    property(warmupLocationPropertyName).orElse(Some(DefaultWarmup))

  override protected def repetitions: Int =
    property(repetitionsPropertyName).map(_.toInt).getOrElse(DefaultRepetitions)

  override protected def csvFileName: Option[String] =
    property(csvFilePropertyName).orElse(Some(DefaultCsv))

  private var extraFilesRegistered = false

  /** Registers [[ExtraFiles]] after the warmup and target directories (which
    * `super.testNames` registers), so that the JVM warmup still runs first.
    */
  override def testNames: Set[String] = {
    super.testNames
    if (!extraFilesRegistered) {
      extraFilesRegistered = true
      ExtraFiles.foreach { resource =>
        // Resolve against the source directories rather than the classpath: silver's test
        // resources are packaged in a jar, which StatisticalTestSuite can't handle.
        val file = ResourceRoots.map(new File(_, resource)).find(_.isFile)
          .getOrElse(fail(s"Benchmark file '$resource' not found in ${ResourceRoots.mkString(", ")}"))
        val prefix = resource.split('/').init.mkString("/")
        registerTest(buildTestInput(file.toPath, prefix))
      }
    }
    super.testNames
  }
}

object SiliconBenchmark {
  val DefaultTarget = "src/test/resources/benchmarks"
  val DefaultWarmup = "src/test/resources/benchmarks-warmup"
  val DefaultRepetitions = 10
  val DefaultCsv: String = {
    val timestamp = java.time.LocalDateTime.now()
      .format(java.time.format.DateTimeFormatter.ofPattern("yyyy-MM-dd_HH-mm-ss"))
    s"target/benchmark_$timestamp.csv"
  }

  /** Files from the regular test suites to benchmark in addition to the target directory,
    * as test resource paths (as in [[SiliconTests]]), resolved against [[ResourceRoots]].
    */
  val ExtraFiles: Seq[String] = Seq(
    "adt/example_2.vpr",                                         // ADTs: constructors, destructors, discriminators
    "adt/termination_mutual_1.vpr",                              // ADTs + mutually recursive termination checks
    "all/basic/disjunction_slow_20.vpr",                         // branching / state joins
    "all/chalice/AVLTree.iterative.vpr",                         // heavy fold/unfold, loops (Chalice)
    "all/domains/domains2.vpr",                                  // domains, axioms
    "all/heap-dependent_triggers/triggerFoldPackage.vpr",        // heap-dependent triggers, fold/package
    "all/issues/silicon/0075_AVLTree.nokeys.vpr",                // large predicate-based program
    "all/issues/silicon/0715_2.vpr",                             // ADTs, maps, decreases
    "all/issues/silicon/0950.vpr",                               // 686 lines, ~50 functions
    "all/issues/silver/0175.vpr",                                // 26-line seq/quantifier stress; mostly Z3 time
    "all/issues/silver/0735.vpr",                                // 694 lines: refute, multisets, maps, forperm, labels
    "all/issues/silver/0875.vpr",                                // QPs + predicates + termination
    "all/maps/example1.vpr",                                     // maps, sets, domains
    "all/permission_introspection/forpermQP.vpr",                // forperm, perm(), QP, wands
    "all/sequences/sequence_incompletenesses.vpr",               // sequences, loops
    "examples/graph-marking/graph-marking.vpr",                  // QP over sets
    "examples/tree-delete-min/tree_delete_min.vpr",              // wands + recursive predicates + loops
    "examples/vmcai2016/arraylist-quantified-permissions.vpr",   // QP + predicates + loops
    "quantifiedcombinations/multiple_quantifiers.vpr",           // mixed QPs, labels/old, functions
    "quantifiedpermissions/misc/functions.vpr",                  // QPs + heap-dependent functions
    "quantifiedpermissions/misc/performance.vpr",                // QP performance regression test
    "quantifiedpermissions/third_party/test_binomial_auto.vpr",  // array-style QPs (VerCors)
    "quantifiedpredicates/examples/list.vpr",                    // quantified predicates, loops
    "termination/functions/basic/allTypes.vpr",                  // termination checks
    "wands/examples_new_syntax/ListIterator.vpr",                // wands + predicates + loops
    "wands/examples_paper/list_insert.vpr",                      // wands: package/apply in loops
    "wands/new_syntax/QPWands.vpr",                              // quantified magic wands
    "wands/regression/conditionals3.vpr",                        // conditional wands, package, perm()
  )

  val ResourceRoots = Seq("src/test/resources", "silver/src/test/resources")
}
