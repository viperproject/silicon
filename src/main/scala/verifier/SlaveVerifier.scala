/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.verifier

import viper.silver.components.StatefulComponent
import viper.silicon._
import viper.silicon.supporters._
import viper.silicon.verifier.BaseVerifier._

class SlaveVerifier(config: Config,
                    uniqueId: String)
    extends BaseVerifier(config, uniqueId)
       with PredicateSupporterProvider[ST, H, S]
       with MethodSupporterProvider[ST, H, S] {

  private val statefulSubcomponents = List[StatefulComponent](
    predicateSupporter,
    methodSupporter
  )

  /* Lifetime */

  override def start() {
    super.start()
    statefulSubcomponents foreach (_.start())
  }

  override def reset() {
    super.reset()
    statefulSubcomponents foreach (_.reset())
  }

  override def stop() {
    super.stop()
    statefulSubcomponents foreach (_.stop())
  }
}
