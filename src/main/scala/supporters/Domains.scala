/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.supporters

import viper.silver.ast
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.common.collections.immutable.InsertionOrderedSet._
import viper.silicon.common.collections.immutable.MultiMap._
import viper.silicon.common.collections.mutable.MMultiMap
import viper.silicon.{MMap, MSet, Map, toMap}
import viper.silicon.interfaces.PreambleContributor
import viper.silicon.interfaces.decider.ProverLike
import viper.silicon.state.{SymbolConverter, terms}
import viper.silicon.state.terms.{Distinct, DomainFun, Sort, Symbol, Term}
import viper.silicon.implicits._

trait DomainsContributor[SO, SY, AX, UA] extends PreambleContributor[SO, SY, AX] {
  def uniquenessAssumptionsAfterAnalysis: Iterable[UA]
  def emitUniquenessAssumptionsAfterAnalysis(sink: ProverLike): Unit
}

class DefaultDomainsContributor(symbolConverter: SymbolConverter,
                                domainTranslator: DomainsTranslator[Term])
    extends DomainsContributor[Sort, DomainFun, Term, Term] {

  /* TODO: Group emitted declarations and axioms by source domain. */

  private var collectedSorts = InsertionOrderedSet[Sort]()
  private var collectedFunctions = InsertionOrderedSet[terms.DomainFun]()
  private var collectedAxioms = InsertionOrderedSet[Term]()
  private var uniqueSymbols = MultiMap.empty[Sort, Symbol]

  /* Lifetime */

  def reset() {
    collectedSorts = collectedSorts.empty
    collectedFunctions = collectedFunctions.empty
    collectedAxioms = collectedAxioms.empty
    uniqueSymbols = MultiMap.empty
  }

  def start() {}
  def stop() {}

  /* Functionality */

  def analyze(program: ast.Program) {
    val concreteDomainTypes = collectConcreteDomainTypes(program)
    val concreteDomainMemberInstances = collectConcreteDomainMemberInstances(program, concreteDomainTypes)

    collectDomainSorts(concreteDomainTypes)
    collectDomainMembers(concreteDomainMemberInstances)
  }

  private def collectDomainSorts(domainTypes: InsertionOrderedSet[ast.DomainType]) {
    assert(domainTypes forall (_.isConcrete), "Expected only concrete domain types")

    domainTypes.foreach(domainType => {
      val domainSort = symbolConverter.toSort(domainType)
      collectedSorts += domainSort
    })
  }

  private def collectDomainMembers(members: Map[ast.Domain, InsertionOrderedSet[DomainMemberInstance]]) {
    /* Since domain member instances come with Sil types, but the corresponding prover declarations
     * work with sorts, it can happen that two instances with different types result in the
     * same function declaration because the types are mapped to the same sort(s).
     *
     * Another source of potential declaration duplication is, that the set of domain member
     * instances can contain two function instances where the type variable mapping of one
     * instance is a subset of the mapping of the other. For example:
     *   function foo(a: A): Int    with (A -> Int)
     *   function foo(a: A): Int    with (A -> Int, B -> Ref)
     * This can happen if the declaring domain contains more type variables than are used by the
     * function.
     *
     * TODO: Prevent such things from happening in the first place, i.e., while collecting all
     *       instances.
     */

    members.foreach{case (_, memberInstances) =>
      assert(memberInstances forall (_.isConcrete), "Expected only concrete domain member instances")

      val functionInstances: InsertionOrderedSet[DomainFunctionInstance] =
        memberInstances collect { case dfi: DomainFunctionInstance => dfi }

      functionInstances.foreach(fi => {
        val inSorts = fi.member.formalArgs map (a => symbolConverter.toSort(a.typ.substitute(fi.typeVarsMap)))
        val outSort = symbolConverter.toSort(fi.member.typ.substitute(fi.typeVarsMap))
        val id = symbolConverter.toSortSpecificId(fi.member.name, inSorts :+ outSort)
        val fct = terms.DomainFun(id, inSorts, outSort)

        collectedFunctions += fct

        if (fi.member.unique) {
          assert(fi.member.formalArgs.isEmpty,
            s"Expected unique domain functions to not take arguments, but found ${fi.member}")

          uniqueSymbols = uniqueSymbols.addBinding(fct.resultSort, fct)
        }
      })
    }

    members.foreach{case (_, memberInstances) =>
      assert(memberInstances forall (_.isConcrete), "Expected only concrete domain member instances")

      val axiomInstances = memberInstances collect {case dai: DomainAxiomInstance => dai}

      axiomInstances.foreach(ai => {
        val tAx = domainTranslator.translateAxiom(ai.member, ai.typeVarsMap)
        collectedAxioms += tAx
      })
    }
  }

  private def domainMembers(domain: ast.Domain): Map[ast.DomainMember, ast.Domain] = {
    val fcts: Seq[(ast.DomainMember, ast.Domain)] = domain.functions.map((_, domain))
    val axms: Seq[(ast.DomainMember, ast.Domain)] = domain.axioms.map((_, domain))

    Map[ast.DomainMember, ast.Domain](fcts ++ axms :_*)
  }

  private def domainMembers(program: ast.Program): Map[ast.DomainMember, ast.Domain] =
    Map(program.domains.flatMap(domainMembers) :_*)

  /**
   * Returns the set of concrete domain types that are used in the given program.
   * @param program A program
   * @return The set of concrete domain types that are used in the given program. For all `dt` in
   *         the returned set, `dt.isConcrete` holds.
   */
  private def collectConcreteDomainTypes(program: ast.Program): InsertionOrderedSet[ast.DomainType] = {
    var domains: InsertionOrderedSet[ast.DomainType] = InsertionOrderedSet()
    var newDomains: InsertionOrderedSet[ast.DomainType] = InsertionOrderedSet()

    var ds: Iterable[ast.DomainType] =
      program.domains filter (_.typVars.isEmpty) map (ast.DomainType(_, Map.empty[ast.TypeVar, ast.Type]))

    domains ++= ds

    ds = collectConcreteDomainTypes(program, Map())
    domains ++= ds

    newDomains = domains
    var continue = newDomains.nonEmpty

    while (continue) {
      newDomains =
        newDomains flatMap (dt => collectConcreteDomainTypes(program.findDomain(dt.domainName), dt.typVarsMap))

      newDomains = newDomains -- domains
      continue = newDomains.nonEmpty

      domains ++= newDomains
    }

    domains
  }

  private def collectConcreteDomainTypes(node: ast.Node, typeVarsMap: Map[ast.TypeVar, ast.Type])
                                        : InsertionOrderedSet[ast.DomainType] = {

    var domains: InsertionOrderedSet[ast.DomainType] = InsertionOrderedSet()

    node visit {
      case t: ast.Typed => t.typ match {
        case dt: ast.DomainType =>
          val substitutedDt = dt.substitute(typeVarsMap)
          if (substitutedDt.isConcrete) domains += substitutedDt

        case _ => /* Ignore other types */
      }
    }

    domains
  }

  private def collectConcreteDomainMemberInstances(program: ast.Program,
                                                   concreteDomainTypes: InsertionOrderedSet[ast.DomainType])
                                                  : Map[ast.Domain, InsertionOrderedSet[DomainMemberInstance]] = {

    val membersWithSource = domainMembers(program)

    val instances = InstanceCollection.empty
    var newInstances = InstanceCollection.empty

    /* Get member instances from concrete domain types. */
    insert(
      instances,
      concreteDomainTypes map (dt => {
        val domain = program.findDomain(dt.domainName)
        val members: MSet[DomainMemberInstance] =
          MSet((domain.functions.map(DomainFunctionInstance(_, dt.typVarsMap))
              ++ domain.axioms.map(DomainAxiomInstance(_, dt.typVarsMap))
              ): _*)

        (domain, members)
        }))

    /* Get member instances from the program. Since the passed type variable mapping is empty,
     * this will only collect domain functions from domain function applications in which all
     * type variables are instantiated with concrete types. This is always the case for domain
     * function applications that occur in program expressions and program assertions because
     * there cannot be any type variables in those contexts, but it is not necessarily the case
     * for domain function applications that occur inside domain declarations.
     */
    insert(newInstances,
           collectConcreteDomainMemberInstances(program, program, Map[ast.TypeVar, ast.Type](), membersWithSource))

    insert(instances, newInstances)

    var continue = newInstances.nonEmpty

    while (continue) {
      val nextNewInstances = InstanceCollection.empty

      newInstances foreach {case (_, memberInstances) =>
        memberInstances foreach {instance =>
          val ms =
            collectConcreteDomainMemberInstances(program,
                                                 membersWithSource(instance.member),
                                                 instance.typeVarsMap,
                                                 membersWithSource)

          insert(nextNewInstances, ms)
      }}

      continue = false

      nextNewInstances foreach {case (domain, memberInstances) =>
        memberInstances foreach {instance =>
          if (!instances.entryExists(domain, _ == instance)) continue = true}}

      newInstances = nextNewInstances
      insert(instances, newInstances)
    }

    val instancesConvertedInnerSets: MMap[ast.Domain, InsertionOrderedSet[DomainMemberInstance]] =
      instances map {case (k, v) => (k, InsertionOrderedSet.empty ++ v)}

    val instancesConvertedOuterMaps: Map[ast.Domain, InsertionOrderedSet[DomainMemberInstance]] =
      toMap(instancesConvertedInnerSets)

    instancesConvertedOuterMaps
  }

  private def collectConcreteDomainMemberInstances(program: ast.Program,
                                                   node: ast.Node,
                                                   typeVarsMap: Map[ast.TypeVar, ast.Type],
                                                   membersWithSource: Map[ast.DomainMember, ast.Domain])
                                                  : InstanceCollection = {

    assert(typeVarsMap.values forall (_.isConcrete), "Expected type variable mapping to only map to concrete types")

    val instances = InstanceCollection.empty

    node visit {
      case dfa: ast.DomainFuncApp =>
        val func = dfa.func(program)
        val combinedTypeVarsMap = typeVarsMap ++ dfa.typVarMap

        if (func.freeTypeVariables forall (v => combinedTypeVarsMap.contains(v) && combinedTypeVarsMap(v).isConcrete)) {
          instances.addBinding(membersWithSource(func), DomainFunctionInstance(func, combinedTypeVarsMap))
        }

      case df: ast.DomainFunc if df.freeTypeVariables forall typeVarsMap.contains =>
        instances.addBinding(membersWithSource(df), DomainFunctionInstance(df, typeVarsMap))

      case da: ast.DomainAxiom if da.freeTypeVariables forall typeVarsMap.contains =>
        instances.addBinding(membersWithSource(da), DomainAxiomInstance(da, typeVarsMap))
    }

    instances
  }

  def sortsAfterAnalysis: Iterable[terms.Sort] = collectedSorts

  def declareSortsAfterAnalysis(sink: ProverLike): Unit = {
    collectedSorts foreach (s => sink.declare(terms.SortDecl(s)))
  }

  def symbolsAfterAnalysis: Iterable[terms.DomainFun] = collectedFunctions

  def declareSymbolsAfterAnalysis(sink: ProverLike): Unit = {
    collectedFunctions foreach (f => sink.declare(terms.FunctionDecl(f)))
  }

  def axiomsAfterAnalysis: Iterable[terms.Term] = collectedAxioms

  def emitAxiomsAfterAnalysis(sink: ProverLike): Unit = {
    collectedAxioms foreach (ax => sink.assume(ax))
  }

  def uniquenessAssumptionsAfterAnalysis: Iterable[Term] =
    uniqueSymbols.map.values map Distinct

  def emitUniquenessAssumptionsAfterAnalysis(sink: ProverLike): Unit = {
    uniquenessAssumptionsAfterAnalysis foreach (t => sink.assume(t))
  }

  def updateGlobalStateAfterAnalysis(): Unit = { /* Nothing to contribute*/ }

  /*
   * Internal declarations
   */

  private sealed trait DomainMemberInstance {
    def member: ast.DomainMember
    def typeVarsMap: Map[ast.TypeVar, ast.Type]

    lazy val typeVars = member.freeTypeVariables
    lazy val isConcrete = typeVars forall typeVarsMap.contains

    override lazy val toString = s"$member where $typeVarsMap"
  }

  private case class DomainFunctionInstance(member: ast.DomainFunc, typeVarsMap: Map[ast.TypeVar, ast.Type])
    extends DomainMemberInstance

  private case class DomainAxiomInstance(member: ast.DomainAxiom, typeVarsMap: Map[ast.TypeVar, ast.Type])
    extends DomainMemberInstance

  private type InstanceCollection =
    MMap[ast.Domain, MSet[DomainMemberInstance]] with MMultiMap[ast.Domain, DomainMemberInstance]

  private object InstanceCollection {
    def empty: InstanceCollection =
      new MMap[ast.Domain, MSet[DomainMemberInstance]] with MMultiMap[ast.Domain, DomainMemberInstance]
  }

  private def insert(into: InstanceCollection, from: Iterable[(ast.Domain, Iterable[DomainMemberInstance])]) {
    from foreach {case (domain, memberInstances) =>
      memberInstances foreach (into.addBinding(domain, _))
    }
  }

  /* For debugging purposes, please don't remove. */

//  private def show(ic: Iterable[(ast.Domain, Iterable[DomainMemberInstance])]) {
//    ic foreach {case (_, memberInstances) =>
//      memberInstances foreach (mi => println("    " + mi))
//    }
//  }
//
//  private def diff(ic1: InstanceCollection, ic2: InstanceCollection): InstanceCollection = {
//    val ic3 = InstanceCollection.empty
//
//    ic1 foreach {case (domain, memberInstances) =>
//      memberInstances foreach {instance =>
//        if (!ic2.entryExists(domain, _ == instance)) ic3.addBinding(domain, instance)}}
//
//    ic3
//  }
}

object DomainPrettyPrinter {
  def show(d: ast.Domain) = d.name + d.typVars.mkString("[",",","]")

  def show(dt: ast.DomainType, program: ast.Program) =
    dt.domainName + program.findDomain(dt.domainName).typVars.mkString("[",",","]") + " where " + dt.typVarsMap
}

trait DomainsTranslator[R] {
  def translateAxiom(ax: ast.DomainAxiom, typeVarMap: Map[ast.TypeVar, ast.Type]): R
}

class DefaultDomainsTranslator(val symbolConverter: SymbolConverter)
    extends DomainsTranslator[Term]
       with ExpressionTranslator {

  def translateAxiom(ax: ast.DomainAxiom, typeVarMap: Map[ast.TypeVar, ast.Type]): Term = {
    val toSort = (typ: ast.Type, localTypeVarMap: Map[ast.TypeVar, ast.Type]) => {
      val concreteType = typ.substitute(localTypeVarMap).substitute(typeVarMap)

      assert(concreteType.isConcrete,
        s"Expected only concrete types, but found $concreteType (${concreteType.getClass.getName}})")

      symbolConverter.toSort(concreteType)
    }

    translate(toSort, InsertionOrderedSet.empty)(ax.exp) match {
      case terms.Quantification(q, vars, body, triggers, "") =>
        terms.Quantification(q, vars, body, triggers, s"prog.${ax.name}")

      case other => other
    }
  }
}
