// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.supporters

import scala.reflect.{ClassTag, classTag}
import viper.silicon.Config
import viper.silicon.state.terms.{Sort, Term, sorts}
import viper.silicon.verifier.Verifier
import viper.silver.ast

class DefaultSequencesContributor(val domainTranslator: DomainsTranslator[Term], config: Config)
    extends BuiltinDomainsContributor {

  type BuiltinDomainType = ast.SeqType
  val builtinDomainTypeTag: ClassTag[BuiltinDomainType] = classTag[ast.SeqType]

  lazy val defaultSourceResource: String = {
    if (Verifier.config.useOldAxiomatization())
      "/dafny_axioms/sequences_old.vpr"
    else
      "/dafny_axioms/sequences.vpr"
  }
  val userProvidedSourceFilepath: Option[String] = config.sequenceAxiomatizationFile.toOption
  val sourceDomainName: String = "$Seq"

  override protected def transformSourceDomainInstance(sequenceDomainInstance: ast.Domain, typ: ast.DomainType): ast.Domain = {
    // sequences.vpr (val sourceResource) contains functions and axioms for generic sequences (Seq[E]), and those
    // for integer sequences (Seq[Int]): currently, function Seq_range and corresponding axioms.
    // Since the function isn't generic but nevertheless included in each sequence domain instance Silicon emits
    // (e.g. part of Seq[Int] and of Seq[Ref]), the function would be declared multiple times on the SMT level,
    // which isn't allowed. In order to prevent this, non-generic functions and axioms are removed from all sequence
    // domain instances but Seq[Int].

    if (typ.typVarsMap.head._2 == ast.Int) {
      sequenceDomainInstance
    } else {
      // TODO: Generalise code once more functions (and/or axioms) are affected
      val functions = sequenceDomainInstance.functions.filterNot(_.name == "Seq_range")
      val axioms = sequenceDomainInstance.axioms.filterNot(a => a.isInstanceOf[ast.NamedDomainAxiom] && a.asInstanceOf[ast.NamedDomainAxiom].name.startsWith("ranged_seq_"))

      sequenceDomainInstance.copy(functions = functions, axioms = axioms)(sequenceDomainInstance.pos, sequenceDomainInstance.info, sequenceDomainInstance.errT)
    }
  }

  def targetSortFactory(argumentSorts: Iterable[Sort]): Sort = {
    assert(argumentSorts.size == 1)
    sorts.Seq(argumentSorts.head)
  }
}
