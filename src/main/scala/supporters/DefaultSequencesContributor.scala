// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.supporters

import scala.reflect.{ClassTag, classTag}
import viper.silicon.Config
import viper.silicon.state.terms.{Sort, Term, sorts}
import viper.silver.ast
import viper.silver.ast.utility.rewriter.Traverse

class DefaultSequencesContributor(val domainTranslator: DomainsTranslator[Term], config: Config)
    extends BuiltinDomainsContributor {

  type BuiltinDomainType = ast.SeqType
  val builtinDomainTypeTag: ClassTag[BuiltinDomainType] = classTag[ast.SeqType]

  val defaultSourceResource: String = "/dafny_axioms/sequences.vpr"
  val userProvidedSourceFilepath: Option[String] = config.sequenceAxiomatizationFile.toOption
  val sourceDomainName: String = "$Seq"

  override protected def transformSourceDomain(sourceDomain: ast.Domain): ast.Domain = {
    // Seq_empty(), if type-wise unconstrained, is typed by Silver as Seq[Int]. However, in
    // case of the sequence source domain, the type should be generic, i.e. Seq[E].
    // Currently, the only affected axiom is hard-coded and appropriately transformed below.
    // See also a comment for axiom "empty_seq_length_zero" in the sequence domain source file
    // (i.e. val sourceResource above).

    sourceDomain transform {
      // TODO: Generalise code once more axioms are affected
      case axiom: ast.NamedDomainAxiom if axiom.name == "empty_seq_length_zero" =>
        axiom transform {
          case app: ast.DomainFuncApp if app.funcname == "Seq_empty" =>
            assert(app.typVarMap.size == 1)

            val (typeVar, typ) = app.typVarMap.head

            if (typ == ast.Int)
              app.copy(typVarMap = Map(typeVar -> typeVar))(app.pos, app.info, app.typ, app.domainName, app.errT)
            else
              app
        }

      /* [2020-03-17 Malte] Potential axiom transformations. Can identify unstable examples,
         but don't seem to gain or cost performance in general. */
      // case eq: ast.EqCmp if eq.left.typ == ast.Bool =>
      //   ast.And(
      //     ast.Implies(eq.left, eq.right)(eq.pos, eq.info, eq.errT),
      //     ast.Implies(eq.right, eq.left)(eq.pos, eq.info, eq.errT),
      //   )(eq.pos, eq.info, eq.errT)
      //
      // case ite: ast.CondExp =>
      //   ast.And(
      //     ast.Implies(ite.cond, ite.thn)(ite.pos, ite.info, ite.errT),
      //     ast.Implies(ast.Not(ite.cond)(ite.pos, ite.info, ite.errT), ite.els)(ite.pos, ite.info, ite.errT)
      //   )(ite.pos, ite.info, ite.errT)
    } //, Traverse.BottomUp)
  }

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
      val axioms = sequenceDomainInstance.axioms.filterNot(_.asInstanceOf[ast.NamedDomainAxiom].name.startsWith("ranged_seq_"))

      sequenceDomainInstance.copy(functions = functions, axioms = axioms)(sequenceDomainInstance.pos, sequenceDomainInstance.info, sequenceDomainInstance.errT)
    }
  }

  def targetSortFactory(argumentSorts: Iterable[Sort]): Sort = {
    assert(argumentSorts.size == 1)
    sorts.Seq(argumentSorts.head)
  }
}
