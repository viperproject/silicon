// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon

import viper.silicon.interfaces.state.NonQuantifiedChunk
import viper.silver.ast
import viper.silicon.rules.PermMapDefinition
import viper.silicon.rules.moreCompleteExhaleSupporter.TaggedSummarisingSnapshot
import viper.silicon.state.terms.Term

package object state {
  type PmCache =
    Map[
      (ast.Resource, Seq[QuantifiedBasicChunk]),
      PermMapDefinition]

  type SsCache =
    Map[
      (ast.Resource, Seq[NonQuantifiedChunk], Seq[Term]),
      (TaggedSummarisingSnapshot, Seq[Term], Term)]
}
