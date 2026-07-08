// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2025 ETH Zurich.

package viper.silicon.supporters

import viper.silicon.Config.JoinMode.JoinMode
import viper.silicon.Config.StateConsolidationMode._
import viper.silicon.Config.{ExhaleMode, JoinMode, StateConsolidationMode}
import viper.silicon.{Map, toMap}
import viper.silver.ast
import viper.silver.reporter.{AnnotationWarning, Reporter}

object AnnotationSupporter {
  val proverConfigAnnotation = "proverConfigArgs"
  val exhaleModeAnnotation = "exhaleMode"
  val joinModeAnnotation = "moreJoins"
  val stateConsolidationModeAnnotation = "stateConsolidationMode"

  def getProverConfigArgs(member: ast.Member, reporter: Reporter): Map[String, String] = {
    member.info.getUniqueInfo[ast.AnnotationInfo] match {
      case Some(ai) if ai.values.contains(proverConfigAnnotation) =>
        toMap(ai.values(proverConfigAnnotation).flatMap(o => {
          val index = o.indexOf("=")
          if (index == -1) {
            reporter report AnnotationWarning(s"Invalid ${proverConfigAnnotation} annotation ${o} on member ${member.name}. " +
              s"Required format for each option is optionName=value.")
            None
          } else {
            val (name, value) = (o.take(index), o.drop(index + 1))
            Some((name, value))
          }
        }))
      case _ =>
        Map.empty
    }
  }

  def getExhaleMode(member: ast.Member, reporter: Reporter): Option[ExhaleMode] = {
    member.info.getUniqueInfo[ast.AnnotationInfo] match {
      case Some(ai) if ai.values.contains(exhaleModeAnnotation) =>
        ai.values(exhaleModeAnnotation) match {
          case Seq("0") | Seq("greedy") =>
            Some(ExhaleMode.Greedy)
          case Seq("1") | Seq("mce") | Seq("moreCompleteExhale") => Some(ExhaleMode.MoreComplete)
          case Seq("2") | Seq("mceOnDemand") =>
            Some(ExhaleMode.MoreCompleteOnDemand)
          case v =>
            reporter report AnnotationWarning(s"Member ${member.name} has invalid ${exhaleModeAnnotation} annotation value $v. Annotation will be ignored.")
            None
        }
      case _ => None
    }
  }

  def getJoinMode(member: ast.Member, reporter: Reporter): Option[JoinMode] = {
    member.info.getUniqueInfo[ast.AnnotationInfo] match {
      case Some(ai) if ai.values.contains(joinModeAnnotation) =>
        ai.values(joinModeAnnotation) match {
          case Seq() | Seq("all") => Some(JoinMode.All)
          case Seq("off") => Some(JoinMode.Off)
          case Seq("impure") => Some(JoinMode.Impure)
          case Seq(vl) =>
            try {
              Some(JoinMode(vl.toInt))
            } catch {
              case _: NumberFormatException =>
                reporter report AnnotationWarning(s"Member ${member.name} has invalid ${joinModeAnnotation} annotation value $vl. Annotation will be ignored.")
                None
            }
          case v =>
            reporter report AnnotationWarning(s"Member ${member.name} has invalid ${joinModeAnnotation} annotation value $v. Annotation will be ignored.")
            None
        }
      case _ => None
    }
  }

  def getStateConsolidationMode(member: ast.Member, reporter: Reporter): Option[StateConsolidationMode] = {
    member.info.getUniqueInfo[ast.AnnotationInfo] match {
      case Some(ai) if ai.values.contains(stateConsolidationModeAnnotation) =>
        val modeAnnotation = ai.values(stateConsolidationModeAnnotation)
        try {
          val mode = modeAnnotation match {
            case Seq("minimal") => Minimal
            case Seq("default") => Default
            case Seq("retrying") => Retrying
            case Seq("minimalRetrying") => MinimalRetrying
            case Seq("moreCompleteExhale") => MoreCompleteExhale
            case Seq("lastRetry") => LastRetry
            case Seq("retryingFailOnly") => RetryingFailOnly
            case Seq("lastRetryFailOnly") => LastRetryFailOnly
            case Seq(v) => StateConsolidationMode(v.toInt)
          }
          Some(mode)
        } catch {
          case _ =>
            reporter report AnnotationWarning(s"Member ${member.name} has invalid ${stateConsolidationModeAnnotation} annotation value. Annotation will be ignored.")
            None
        }
      case _ => None
    }
  }
}
