// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package rpi

import org.rogach.scallop.{ScallopConf, ScallopOption}

import scala.util.Properties

/**
  * A configuration for the inference.
  */
class Configuration(arguments: Seq[String]) extends ScallopConf(arguments) {
  val z3: ScallopOption[String] =
    opt[String](
      name = "z3",
      descr = "The path to the z3 executable",
      default = Properties.envOrNone("Z3_EXE"),
      required = true)

  val maxRounds: ScallopOption[Int] =
    opt[Int](
      name = "maxRounds",
      descr = "The number of rounds after which the learner gets exhausted and gives up.",
      default = Some(20))

  val maxClauses: ScallopOption[Int] =
    opt[Int](
      name = "maxClauses",
      descr = "The maximal number of clauses that may be used for a guard.",
      default = Some(1))

  val maxLength: ScallopOption[Int] =
    opt[Int](
      name = "maxLength",
      descr = "The maximal length of access paths that may appear in specifications.",
      default = Some(2))

  /**
    * Note: The verifier uses heuristics if the use of annotations is disabled. The heuristics implemented in th silicon
    * verifier are currently experimental and limited to folds and unfolds.
    */
  val useAnnotations: ScallopOption[Boolean] =
    opt[Boolean](
      name = "useAnnotations",
      descr = "Enables the use of annotations.")

  /**
    * Note: Only there to have means to make sure annotations are disabled.
    */
  val useHeuristics: ScallopOption[Boolean] =
    opt[Boolean](
      name = "useHeuristics",
      descr = "Explicitly forbids the use of annotations.",
      default = useAnnotations.map { value => !value }.toOption)

  /**
    * Note: Since silicon is a iso-recursive verifier, we force additional folds in positions where a predicate needs
    * to be established, such that we only have to rely on unfold heuristics (as failing fold heuristics may yield
    * incorrect samples). This parameter regulates up to which depth the inference statically fold predicates.
    */
  val heuristicsFoldDepth: ScallopOption[Int] =
    opt[Int](
      name = "heuristicsFoldDepth",
      descr = "The depth up to which predicates are statically folded when the heuristics is enabled.",
      default = Some(1))

  val noPredicates: ScallopOption[Boolean] =
    opt[Boolean](
      name = "noPredicates",
      descr = "Disables the use of recursive predicates.")

  val usePredicates: ScallopOption[Boolean] =
    noPredicates.map { value => !value }

  val useSegments: ScallopOption[Boolean] =
    opt[Boolean](
      name = "useSegments",
      descr = "Enables the use of predicate segments.")

  val restrictTruncation: ScallopOption[Boolean] =
    opt[Boolean](
      name = "restrictTruncation",
      descr = "Enables the restriction of truncation arguments to options appearing in samples.")

  val noInlining: ScallopOption[Boolean] =
    opt[Boolean](
      name = "noInlining",
      descr = "Disables specification inlining.",
      hidden = true)

  val noBranching: ScallopOption[Boolean] =
    opt[Boolean](
      name = "noBranching",
      descr = "Disables branching on atomic predicates.",
      hidden = true)

  val noBatching: ScallopOption[Boolean] =
    opt[Boolean](
      name = "noBatching",
      descr = "Disables batch verification of checks.",
      hidden = true)

  val verifyWithHints: ScallopOption[Boolean] =
    opt[Boolean](
      name = "verifyWithAnnotations",
      hidden = true)

  val logLevel: ScallopOption[String] =
    opt[String](
      name="logLevel",
      descr = "One of the following log levels: ALL, TRACE, DEBUG, INFO, WARN, ERROR, OFF.",
      default = None)

  val path: ScallopOption[String] =
    trailArg[String](
      name = "path",
      descr = "The path to the input file or folder.")

  mutuallyExclusive(useHeuristics, useAnnotations)
  mutuallyExclusive(useSegments, noPredicates)
  dependsOnAll(restrictTruncation, List(useSegments))

  verify()
}
