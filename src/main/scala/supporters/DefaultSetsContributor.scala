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

class DefaultSetsContributor(val domainTranslator: DomainsTranslator[Term], config: Config)
    extends BuiltinDomainsContributor {

  type BuiltinDomainType = ast.SetType
  val builtinDomainTypeTag: ClassTag[BuiltinDomainType] = classTag[ast.SetType]

  val defaultSourceResource: String = "/dafny_axioms/sets.vpr"
  val userProvidedSourceFilepath: Option[String] = config.setAxiomatizationFile.toOption
  val sourceDomainName: String = "$Set"

  override def computeGroundTypeInstances(program: ast.Program): InsertionOrderedSet[ast.SetType] = {
    var setTypeInstances = super.computeGroundTypeInstances(program)

    /* Axioms generated for quantified permissions depend on sets.
     * Hence, we add the appropriate set types iff quantified permissions are used in the program.
     *
     * TODO: It shouldn't be the responsibility of the sets contributor to add set types
     *       required by QPs
     */
    if (program.existsDefined { case f: ast.Forall if (f.triggers flatMap (_.exps)) exists (e => e.existsDefined { case _: ast.ResourceAccess => }) =>
      case q: ast.QuantifiedExp if !q.isPure => }) {
      program.fields foreach {f => setTypeInstances += ast.SetType(f.typ)}

      setTypeInstances += ast.SetType(ast.Ref) /* $FVF.domain_f is ref-typed */
    }

    setTypeInstances
  }

  def targetSortFactory(argumentSorts: Iterable[Sort]): Sort = {
    assert(argumentSorts.size == 1)
    sorts.Set(argumentSorts.head)
  }
}

