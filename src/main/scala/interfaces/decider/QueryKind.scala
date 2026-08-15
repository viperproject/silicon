// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.interfaces.decider

/** Identifies the kind of solver interaction recorded in a [[viper.silicon.reporting.ProofQueryRecord]]. */
sealed trait QueryKind

object QueryKind {
  case object Assert extends QueryKind { override def toString = "assert" }
  case object Check  extends QueryKind { override def toString = "check"  }
  case object Push   extends QueryKind { override def toString = "push"   }
  case object Pop    extends QueryKind { override def toString = "pop"    }
}
