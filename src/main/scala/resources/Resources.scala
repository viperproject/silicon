/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.resources

import viper.silicon.Map

object Resources {
  val resourceDescriptions: Map[ResourceID, ResourceDescription] = Map(
        PredicateID() -> new PredicateDescription,
        FieldID() -> new FieldDescription,
        MagicWandID() -> new MagicWandDescription
      )
}

sealed abstract class ResourceID
sealed abstract class BaseID extends ResourceID

case class PredicateID() extends BaseID
case class FieldID() extends BaseID
case class MagicWandID() extends ResourceID