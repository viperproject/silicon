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
import viper.silicon.verifier.Verifier

class DefaultSetsContributor(val domainTranslator: DomainsTranslator[Term], config: Config)
    extends BuiltinDomainsContributor {

  type BuiltinDomainType = ast.SetType
  val builtinDomainTypeTag: ClassTag[BuiltinDomainType] = classTag[ast.SetType]

  lazy val defaultSourceResource: String = {
    if (Verifier.config.useOldAxiomatization())
      "/dafny_axioms/sets_old.vpr"
    else
      "/dafny_axioms/sets.vpr"
  }
  val userProvidedSourceFilepath: Option[String] = config.setAxiomatizationFile.toOption
  val sourceDomainName: String = "$Set"

  override def computeGroundTypeInstances(program: ast.Program): InsertionOrderedSet[ast.SetType] = {
    var setTypeInstances = super.computeGroundTypeInstances(program)

    /* Axioms generated for quantified permissions depend on sets.
     * Hence, we add the appropriate set types iff quantified permissions are used in the program.
     *
     * TODO: It shouldn't be the responsibility of the sets contributor to add set types
     *       required by QPs. Rather, this should be done by DefaultFieldValueFunctionContributor
     *       and DefaultPredicateAndWandSnapFunctionsContributor.
     *       However, it is currently not (easily) possible for the latter to contribute instances
     *       of set axioms.
     */
    if (program.existsDefined {
      case f: ast.Forall if (f.triggers flatMap (_.exps)) exists (e => e.existsDefined { case _: ast.ResourceAccess => }) =>
      case q: ast.Exists if (q.triggers flatMap (_.exps)) exists (e => e.existsDefined { case _: ast.ResourceAccess => }) =>
      case q: ast.QuantifiedExp if !q.isPure =>
    }) {
      program.fields foreach {f => setTypeInstances += ast.SetType(f.typ)}

      setTypeInstances += ast.SetType(ast.Ref) /* $FVF.domain_f is of type Set[Ref] */

      /* $PSF.domain_p is of type Set[Snap], and a corresponding instantiation of the set axioms
       * is thus needed. Currently, such an instantiation is supported only for Viper types.
       * Hence, we use an embedding of Silicon's sorts.Snap into Viper's type system, via a Viper
       * extension type. */
      setTypeInstances += ast.SetType(viper.silicon.utils.ast.ViperEmbedding(sorts.Snap))
    }

    /* The domain of maps depend on sets, for representing the domain and codomain/range of any map.
     * Hence, for every instance of a map type found in the program, we add the appropriate set types.
     *
     * TODO: It should not be the responsibility of the set contributor to add set types required for maps.
     *       However, there currently doesn't seem to be a good way to do this elsewhere.
     */
    setTypeInstances ++= program.groundTypeInstances.collect {
      case ast.MapType(keyType, valueType) => Set(ast.SetType(keyType), ast.SetType(valueType))
    }.flatten

    setTypeInstances
  }

  def targetSortFactory(argumentSorts: Iterable[Sort]): Sort = {
    assert(argumentSorts.size == 1)
    sorts.Set(argumentSorts.head)
  }
}
