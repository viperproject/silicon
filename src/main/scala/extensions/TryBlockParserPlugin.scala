// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2020 ETH Zurich.

package viper.silicon.extensions

import viper.silver.parser.FastParser
import viper.silver.plugin.{ParserPluginTemplate, SilverPlugin}

class TryBlockParserPlugin(fp: FastParser) extends SilverPlugin with ParserPluginTemplate {
  import fastparse._
  import viper.silver.parser.FastParserCompanion.whitespace
  import fp.{FP, block, ParserExtension}


  private val tryKeyword = "try"

  def tryBlock[_:P]: P[PTryBlock] =FP("try" ~/ block) map { case (pos, s) => PTryBlock(s)(pos) }

  override def beforeParse(input: String, isImported: Boolean): String = {
    ParserExtension.addNewKeywords(Set(tryKeyword))
    ParserExtension.addNewStmtAtEnd(tryBlock(_))

    input
  }
}
