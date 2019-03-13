// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.resources

import viper.silicon.Map

object Resources {
  val resourceDescriptions: Map[ResourceID, ResourceDescription] =
    Map(PredicateID -> new PredicateDescription,
        FieldID-> new FieldDescription,
        MagicWandID -> new MagicWandDescription)
}

sealed abstract class ResourceID
sealed abstract class BaseID extends ResourceID

case object PredicateID extends BaseID
case object FieldID extends BaseID
case object MagicWandID extends ResourceID
