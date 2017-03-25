/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.supporters

import scala.reflect.{ClassTag, classTag}
import viper.silver.ast
import viper.silicon.state.terms._

class DefaultMultisetsContributor(val domainTranslator: DomainsTranslator[Term])
    extends BuiltinDomainsContributor {

  type BuiltinDomainType = ast.MultisetType
  val builtinDomainTypeTag: ClassTag[BuiltinDomainType] = classTag[ast.MultisetType]

  val sourceResource: String = "/dafny_axioms/multisets.vpr"
  def sourceDomainName: String = "$Multiset"

  def targetSortFactory(argumentSorts: Iterable[Sort]): Sort = {
    assert(argumentSorts.size == 1)
    sorts.Multiset(argumentSorts.head)
  }
}


