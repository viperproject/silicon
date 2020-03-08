// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.supporters

import scala.reflect.{ClassTag, classTag}
import viper.silicon.Config
import viper.silver.ast
import viper.silicon.state.terms._

class DefaultMultisetsContributor(val domainTranslator: DomainsTranslator[Term], config: Config)
    extends BuiltinDomainsContributor {

  type BuiltinDomainType = ast.MultisetType
  val builtinDomainTypeTag: ClassTag[BuiltinDomainType] = classTag[ast.MultisetType]

  val defaultSourceResource: String = "/dafny_axioms/multisets.vpr"
  val userProvidedSourceFilepath: Option[String] = config.multisetAxiomatizationFile.toOption
  val sourceDomainName: String = "$Multiset"

  def targetSortFactory(argumentSorts: Iterable[Sort]): Sort = {
    assert(argumentSorts.size == 1)
    sorts.Multiset(argumentSorts.head)
  }
}
