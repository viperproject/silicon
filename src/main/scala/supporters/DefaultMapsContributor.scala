// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.supporters

import scala.reflect.{ClassTag, classTag}
import viper.silicon.Config
import viper.silver.ast
import viper.silicon.state.terms.{Sort, Term, sorts}

class DefaultMapsContributor(val domainTranslator: DomainsTranslator[Term], config: Config) extends BuiltinDomainsContributor {

  override type BuiltinDomainType = ast.MapType

  val builtinDomainTypeTag: ClassTag[BuiltinDomainType] = classTag[ast.MapType]

  override def defaultSourceResource: String = "/dafny_axioms/maps.vpr"

  override def userProvidedSourceFilepath: Option[String] = config.mapAxiomatizationFile.toOption

  override def sourceDomainName: String = "$Map"

  override def targetSortFactory(argumentSorts: Iterable[Sort]): Sort = {
    assert(argumentSorts.size == 2)
    sorts.Map(argumentSorts.head, argumentSorts.tail.head)
  }
}
