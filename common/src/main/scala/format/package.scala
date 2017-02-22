/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.common

package object format {
  def formatMillisReadably(millis: Long): String = {
    import java.util.concurrent.TimeUnit

    val MINUTE = TimeUnit.MINUTES.toMillis(1)
    val HOUR = TimeUnit.HOURS.toMillis(1)

    if (millis < MINUTE)
      "%1$02.2fs".format(millis.toFloat / 1000)
    else if (millis < HOUR)
      "%1$TMm:%1$TSs".format(millis)
    else
      "%dh:%2$TMm:%2$TSs".format(millis / HOUR, millis % HOUR)
  }
}
