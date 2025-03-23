// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.supporters

import scala.reflect.{ClassTag, classTag}
import viper.silicon.Config
import viper.silver.ast
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.state.terms.{Sort, Term, sorts}

import scala.reflect.{ClassTag, classTag}

class DefaultSetsContributor2(val domainTranslator: DomainsTranslator[Term], config: Config)
    extends BuiltinDomainsContributor {

  type BuiltinDomainType = ast.SetType
  val builtinDomainTypeTag: ClassTag[BuiltinDomainType] = classTag[ast.SetType]

  val defaultSourceResource: String = "/dafny_axioms/sets_ref.vpr"
  val userProvidedSourceFilepath: Option[String] = config.setAxiomatizationFile.toOption
  val sourceDomainName: String = "$Set"

  override def computeGroundTypeInstances(program: ast.Program): InsertionOrderedSet[ast.SetType] = {
    val setTypeInstances: InsertionOrderedSet[ast.SetType] = InsertionOrderedSet(ast.SetType(viper.silicon.utils.ast.ViperEmbedding(sorts.QPRef))) /* $FVF.domain_f is of type Set[Ref] */

    setTypeInstances
  }

  def targetSortFactory(argumentSorts: Iterable[Sort]): Sort = {
    assert(argumentSorts.size == 1)
    sorts.Set(argumentSorts.head)
  }
}
