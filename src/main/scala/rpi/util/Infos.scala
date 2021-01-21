package rpi.util

import viper.silver.ast

trait ValueInfo extends ast.Info {
  override def comment: Seq[String] = Seq.empty

  override def isCached: Boolean = false
}