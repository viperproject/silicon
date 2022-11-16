// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2022 ETH Zurich.

package viper.silicon.rules

import viper.silicon.interfaces.VerificationResult
import viper.silicon.interfaces.state.CarbonChunk
import viper.silicon.rules.quantifiedChunkSupporter.createFailure
import viper.silicon.state.terms.{Term, Var}
import viper.silicon.state.{ChunkIdentifier, Heap, State}
import viper.silicon.verifier.Verifier
import viper.silver.verifier.PartialVerificationError
import viper.silver.ast
import viper.silver.verifier.reasons.{InsufficientPermission, MagicWandChunkNotFound}

class CarbonQuantifiedChunkSupport extends SymbolicExecutionRules {

}

object carbonQuantifiedChunkSupporter extends CarbonQuantifiedChunkSupport {

  def consumeSingleLocation(s: State,
                            h: Heap,
                            codomainQVars: Seq[Var], /* rs := r_1, ..., r_m */
                            arguments: Seq[Term], // es := e_1, ..., e_n
                            resourceAccess: ast.ResourceAccess,
                            permissions: Term, /* p */
                            pve: PartialVerificationError,
                            v: Verifier)
                           (Q: (State, Heap, Term, Verifier) => VerificationResult)
  : VerificationResult = {
    val resource = resourceAccess.res(s.program)
    val failure = resourceAccess match {
      case locAcc: ast.LocationAccess => createFailure(pve dueTo InsufficientPermission(locAcc), v, s)
      case wand: ast.MagicWand => createFailure(pve dueTo MagicWandChunkNotFound(wand), v, s)
      case _ => sys.error(s"Found resource $resourceAccess, which is not yet supported as a quantified resource.")
    }

    val chunkIdentifier = ChunkIdentifier(resource, s.program)
    if (s.exhaleExt) {
      ???
    } else {
      // find chunk
      h.values.find {
        case cc: CarbonChunk if cc.id == chunkIdentifier => true
        case _ => false
      }

      // assert sufficient
      v.decider.assert()

      // create snapshot :( can i do this without droping lots of
    }
  }
}
