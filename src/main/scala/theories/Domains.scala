package semper
package silicon
package theories

import interfaces.decider.Prover
import interfaces.PreambleEmitter
import state.terms
import state.terms.Term
import state.SymbolConvert
import state.terms.implicits._
import reporting.VerificationException
import implicits._

trait DomainsEmitter extends PreambleEmitter {
  def emitUniquenessAssumptions()
}

class DefaultDomainsEmitter(domainTranslator: DomainsTranslator[Term], prover: Prover, symbolConverter: SymbolConvert)
    extends DomainsEmitter {

  /* TODO: Group emitted declarations and axioms by source domain. */

  private var collectedSorts = Set[terms.Sort]()
  private var collectedSymbols = Set[terms.Function]()
  private var collectedAxioms = Set[terms.Term]()

  private var uniqueSymbols = Set[terms.Term]()
    /* The type is Set[terms.Term] and not Set[terms.Function], because immutable sets - unlike immutable
     * lists - are invariant in their element type. See http://stackoverflow.com/questions/676615/ for explanations.
     * Since terms.Distinct takes a Set[terms.Term], a Set[terms.Function] cannot be passed.
     */

  def sorts = collectedSorts
  def symbols = Some(collectedSymbols)

  /* Lifetime */

  def reset() {
    collectedSorts = collectedSorts.empty
    collectedSymbols = collectedSymbols.empty
    collectedAxioms = collectedAxioms.empty
    uniqueSymbols = uniqueSymbols.empty
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

  private def collectDomainSorts(domainTypes: Set[ast.types.DomainType]) {
    assert(domainTypes forall (_.isConcrete), "Expected only concrete domain types")

    domainTypes.foreach(domainType => {
      val domainSort = symbolConverter.toSort(domainType)
      collectedSorts += domainSort
    })
  }

  def declareSorts() {
    collectedSorts foreach (s => prover.declare(terms.SortDecl(s)))
  }

  private def collectDomainMembers(members: Map[ast.Domain, Set[DomainMemberInstance]]) {
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

    members.foreach{case (domain, memberInstances) =>
      assert(memberInstances forall (_.isConcrete), "Expected only concrete domain member instances")

      val functionInstances = memberInstances collect {case dfi: DomainFunctionInstance => dfi}

      functionInstances.foreach(fi => {
        val inSorts = fi.member.formalArgs map (a => symbolConverter.toSort(a.typ.substitute(fi.typeVarsMap)))
        val outSort = symbolConverter.toSort(fi.member.typ.substitute(fi.typeVarsMap))
        val id = symbolConverter.toSortSpecificId(fi.member.name, inSorts :+ outSort)
        val fct = terms.Function(id, inSorts, outSort)

        collectedSymbols += fct

        if (fi.member.unique) {
          assert(fi.member.formalArgs.isEmpty,
            s"Expected unique domain functions to not take arguments, but found ${fi.member}")

          uniqueSymbols += fct
        }
      })
    }

    members.foreach{case (domain, memberInstances) =>
      assert(memberInstances forall (_.isConcrete), "Expected only concrete domain member instances")

      val axiomInstances = memberInstances collect {case dai: DomainAxiomInstance => dai}

      axiomInstances.foreach(ai => {
        val tAx = domainTranslator.translateAxiom(ai.member, ai.typeVarsMap)
        collectedAxioms += tAx
      })
    }
  }

  def declareSymbols() {
    collectedSymbols foreach {function =>
      val functionDecl = terms.FunctionDecl(function)
      prover.declare(functionDecl)
    }
  }

  def emitAxioms() {
    collectedAxioms foreach prover.assume
  }

  def emitUniquenessAssumptions() {
    prover.assume(terms.Distinct(uniqueSymbols))
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
  private def collectConcreteDomainTypes(program: ast.Program): Set[ast.types.DomainType] = {
    var domains: Set[ast.types.DomainType] = Set()
    var newDomains: Set[ast.types.DomainType] = Set()

    var ds: Iterable[ast.types.DomainType] =
      program.domains filter (_.typVars.isEmpty) map (ast.types.DomainType(_, Map.empty[ast.TypeVar, ast.Type]))

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
                                        : Set[ast.types.DomainType] = {

    var domains: Set[ast.types.DomainType] = Set()

    node visit {
      case t: ast.Typed => t.typ match {
        case dt: ast.types.DomainType =>
          val substitutedDt = dt.substitute(typeVarsMap)
          if (substitutedDt.isConcrete) domains += substitutedDt

        case _ => /* Ignore other types */
      }
    }

    domains
  }

  private def collectConcreteDomainMemberInstances(program: ast.Program, concreteDomainTypes: Set[ast.types.DomainType])
                                                  : Map[ast.Domain, Set[DomainMemberInstance]] = {

    val membersWithSource = domainMembers(program)

    val instances = InstanceCollection.empty
    var newInstances = InstanceCollection.empty

    /* Get member instances from concrete domain types. */
    insert(
      instances,
      concreteDomainTypes map {case dt =>
        val domain = program.findDomain(dt.domainName)
        val members: MSet[DomainMemberInstance] =
          MSet((domain.functions.map(DomainFunctionInstance(_, dt.typVarsMap))
                ++ domain.axioms.map(DomainAxiomInstance(_, dt.typVarsMap))
               ):_*)

        (domain, members)})

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

      newInstances foreach {case (domain, memberInstances) =>
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

    val instancesConvertedInnerSets: MMap[ast.Domain, Set[DomainMemberInstance]] =
      instances map {case (k, v) => (k, Set.empty ++ v)}

    val instancesConvertedOuterMaps: Map[ast.Domain, Set[DomainMemberInstance]] =
      Map.empty ++ instancesConvertedInnerSets

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

      case df: ast.DomainFunction if df.freeTypeVariables forall typeVarsMap.contains =>
        instances.addBinding(membersWithSource(df), DomainFunctionInstance(df, typeVarsMap))

      case da: ast.DomainAxiom if da.freeTypeVariables forall typeVarsMap.contains =>
        instances.addBinding(membersWithSource(da), DomainAxiomInstance(da, typeVarsMap))
    }

    instances
  }

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

  private case class DomainFunctionInstance(member: ast.DomainFunction, typeVarsMap: Map[ast.TypeVar, ast.Type])
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

  private def show(ic: Iterable[(ast.Domain, Iterable[DomainMemberInstance])]) {
    ic foreach {case (domain, memberInstances) =>
      memberInstances foreach (mi => println("    " + mi))
    }
  }

  private def diff(ic1: InstanceCollection, ic2: InstanceCollection): InstanceCollection = {
    val ic3 = InstanceCollection.empty

    ic1 foreach {case (domain, memberInstances) =>
      memberInstances foreach {instance =>
        if (!ic2.entryExists(domain, _ == instance)) ic3.addBinding(domain, instance)}}

    ic3
  }
}

object DomainPrettyPrinter {
  def show(d: ast.Domain) = d.name + d.typVars.mkString("[",",","]")

  def show(dt: ast.types.DomainType, program: ast.Program) =
    dt.domainName + program.findDomain(dt.domainName).typVars.mkString("[",",","]") + " where " + dt.typVarsMap
}

trait DomainsTranslator[R] {
  def translateAxiom(ax: ast.DomainAxiom, typeVarMap: Map[ast.TypeVar, ast.Type]): R
}

class DefaultDomainsTranslator(symbolConverter: SymbolConvert) extends DomainsTranslator[Term] {
  def translateAxiom(ax: ast.DomainAxiom, typeVarMap: Map[ast.TypeVar, ast.Type]): Term = {
    val toSort = (typ: ast.Type, localTypeVarMap: Map[ast.TypeVar, ast.Type]) => {
      val concreteType = typ.substitute(localTypeVarMap).substitute(typeVarMap)

      assert(concreteType.isConcrete,
             s"Expected only concrete types, but found $concreteType (${concreteType.getClass.getName}})")

      symbolConverter.toSort(concreteType)
    }

    translateExp(toSort)(ax.exp)
  }

  /**
    *
    * @param toSort
    * @param exp
    * @return
    *
    * TODO: Shares a lot of code with DefaultEvaluator. Unfortunately, it doesn't seem to be easy to
    *       reuse code because the code in DefaultEvaluator uses the state whereas this one here
    *       doesn't. Of course, one could just evaluate the domains using the DefaultEvaluator - which
    *       was done before - but that is less efficient and creates lots of additional noise output
    *       in the prover log.
    */
  private def translateExp(toSort: (ast.Type, Map[ast.TypeVar, ast.Type])  => terms.Sort)
                          (exp: ast.Expression)
                          : Term = {

    val f = translateExp(toSort) _

    exp match {
      case q @ ast.Quantified(qvars, body) =>
        val quantifier = q match {
          case _: ast.Forall => terms.Forall
          case _: ast.Exists => terms.Exists
        }
        /* TODO: Translate triggers as well */
        terms.Quantification(quantifier, qvars map (v => terms.Var(v.name, toSort(v.typ, Map()))), f(body))

      case ast.True() => terms.True()
      case ast.False() => terms.False()
      case ast.Not(e0) => terms.Not(f(e0))
      case ast.And(e0, e1) => terms.And(f(e0), f(e1))
      case ast.Or(e0, e1) => terms.Or(f(e0), f(e1))
      case ast.Implies(e0, e1) => terms.Implies(f(e0), f(e1))
      case ast.Ite(e0, e1, e2) => terms.Ite(f(e0), f(e1), f(e2))

      case ast.Equals(e0, e1) => terms.Eq(f(e0), f(e1))
      case ast.Unequals(e0, e1) => terms.Not(terms.Eq(f(e0), f(e1)))

      case ast.IntegerLiteral(n) => terms.IntLiteral(n)
      case ast.IntPlus(e0, e1) => terms.Plus(f(e0), f(e1))
      case ast.IntMinus(e0, e1) => terms.Minus(f(e0), f(e1))
      case ast.IntTimes(e0, e1) => terms.Times(f(e0), f(e1))
      case ast.IntDiv(e0, e1) => terms.Div(f(e0), f(e1))
      case ast.IntMod(e0, e1) => terms.Mod(f(e0), f(e1))
      case ast.IntNeg(e0) => terms.Minus(0, f(e0))

      case ast.IntGE(e0, e1) => terms.AtLeast(f(e0), f(e1))
      case ast.IntGT(e0, e1) => terms.Greater(f(e0), f(e1))
      case ast.IntLE(e0, e1) => terms.AtMost(f(e0), f(e1))
      case ast.IntLT(e0, e1) => terms.Less(f(e0), f(e1))

      case ast.NullLiteral() => terms.Null()

      case v: ast.Variable => terms.Var(v.name, toSort(v.typ, Map()))

      case ast.DomainFuncApp(functionName, args, typeVarMap) =>
        val tArgs = args map f
        val inSorts = tArgs map (_.sort)
        val outSort = toSort(exp.typ, typeVarMap)
        val id = symbolConverter.toSortSpecificId(functionName, inSorts :+ outSort)
        val df = terms.Function(id, inSorts, outSort)
        terms.DomainFApp(df, tArgs)

      case _: ast.FullPerm => terms.FullPerm()
      case _: ast.NoPerm => terms.NoPerm()
      case ast.FractionalPerm(e0, e1) => terms.FractionPerm(terms.TermPerm(f(e0)), terms.TermPerm(f(e1)))

      case ast.PermPlus(e0, e1) => terms.PermPlus(terms.TermPerm(f(e0)), terms.TermPerm(f(e1)))
      case ast.PermMinus(e0, e1) => terms.PermMinus(terms.TermPerm(f(e0)), terms.TermPerm(f(e1)))
      case ast.PermTimes(e0, e1) => terms.PermTimes(terms.TermPerm(f(e0)), terms.TermPerm(f(e1)))
      case ast.IntPermTimes(e0, e1) => terms.IntPermTimes(f(e0), terms.TermPerm(f(e1)))
      case ast.PermLE(e0, e1) => terms.AtMost(f(e0), f(e1))
      case ast.PermLT(e0, e1) => terms.Less(f(e0), f(e1))
      case ast.PermGE(e0, e1) => terms.AtLeast(f(e0), f(e1))
      case ast.PermGT(e0, e1) => terms.Greater(f(e0), f(e1))

      case sil.ast.SeqAppend(e0, e1) => terms.SeqAppend(f(e0), f(e1))
      case sil.ast.SeqContains(e0, e1) => terms.SeqIn(f(e1), f(e0))
      case sil.ast.SeqDrop(e0, e1) => terms.SeqDrop(f(e0), f(e1))
      case sil.ast.SeqIndex(e0, e1) => terms.SeqAt(f(e0), f(e1))
      case sil.ast.SeqLength(e) => terms.SeqLength(f(e))
      case sil.ast.SeqTake(e0, e1) => terms.SeqTake(f(e0), f(e1))
      case sil.ast.EmptySeq(typ) => terms.SeqNil(toSort(typ, Map()))
      case sil.ast.RangeSeq(e0, e1) => terms.SeqRanged(f(e0), f(e1))
      case sil.ast.SeqUpdate(e0, e1, e2) => terms.SeqUpdate(f(e0), f(e1), f(e2))

      case sil.ast.ExplicitSeq(es) =>
        es.tail.foldLeft[terms.SeqTerm](terms.SeqSingleton(f(es.head)))((tSeq, e) =>
            terms.SeqAppend(terms.SeqSingleton(f(e)), tSeq))

      case   _: ast.LocationAccess | _: ast.AccessPredicate | _: sil.ast.OldExp | _: ast.FractionalPerm
           | _: ast.ResultLiteral | _: ast.Unfolding | _: ast.InhaleExhale | _: ast.PredicateAccess
           | _: ast.FuncApp | _: ast.CurrentPerm | _: ast.EpsilonPerm | _: ast.WildcardPerm
           | _: sil.ast.MultisetExp | _: sil.ast.EmptySet | _: sil.ast.ExplicitSet
           | _: ast.Applying | _: ast.Folding | _: ast.MagicWand | _: ast.Packaging =>

        throw VerificationException(ast.Consistency.createUnexpectedNodeDuringDomainTranslationError(exp))
    }
  }
}
