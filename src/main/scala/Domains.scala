package semper
package silicon

import scala.language.postfixOps
import collection.mutable.{HashMap => MHashMap, MultiMap => MMultiMap, Set => MSet}
import semper.sil.ast._
import interfaces.decider.Prover
import state.terms
import state.terms.Term
import state.terms.implicits._
import state.SymbolConvert

trait DomainEmitter {
  def reset()
  def declaredSorts: Set[terms.Sort]
  def declaredSymbols: Set[terms.Function]
  def emitDomains(program: Program)
}

class DefaultDomainEmitter(domainTranslator: DomainTranslator[Term], prover: Prover, symbolConverter: SymbolConvert)
    extends DomainEmitter {

  private var sorts = Set[terms.Sort]()
  private var symbols = Set[terms.Function]()

  def reset() {
    sorts = sorts.empty
    symbols = symbols.empty
  }

  def declaredSorts = sorts
  def declaredSymbols = symbols

  def emitDomains(program: Program) {
    val concreteDomainTypes = collectConcreteDomainTypes(program)
    val concreteDomainMemberInstances = collectConcreteDomainMemberInstances(program, concreteDomainTypes)

    emitDomainDeclarations(concreteDomainTypes)
    emitDomainMembers(concreteDomainMemberInstances)
  }

  private def emitDomainDeclarations(domainTypes: Set[DomainType]) {
    assert(domainTypes forall (_.isConcrete), "Expected only concrete domain types")

    prover.logComment("")
    prover.logComment("Declaring additional domains")
    prover.logComment("")

    /* Declare domains. */
    domainTypes.foreach(domainType => {
      prover.logComment("Declaring domain " + domainType)

      val domainSort = symbolConverter.toSort(domainType)
      sorts += domainSort

      prover.declare(terms.SortDecl(domainSort))
    })
  }

  /* Declare functions and predicates of each domain.
   * Since these can reference arbitrary other domains, it is crucial that all domains have
   * already been declared.
   */
  private def emitDomainMembers(members: Map[Domain, Set[DomainMemberInstance]]) {
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

    /* Functions must be declared first, because they can be mentioned in axioms. */

    var uniqueFunctions: Set[terms.Term] = Set()
      /* The type is Set[terms.Term] and not Set[terms.Function], because immutable sets - unlike immutable
       * lists - are invariant in their element type. See http://stackoverflow.com/questions/676615/ for explanations.
       * Since terms.Distinct takes a Set[terms.Term], a Set[terms.Function] cannot be passed.
       */

    members.foreach{case (domain, memberInstances) =>
      assert(memberInstances forall (_.isConcrete), "Expected only concrete domain member instances")

      val functionInstances = memberInstances collect {case dfi: DomainFunctionInstance => dfi}

      prover.logComment("Functions of " + DomainPrettyPrinter.show(domain))

      functionInstances.foreach(fi => {
        //        decider.prover.logComment(fi.toString)
        val inSorts = fi.member.formalArgs map (a => symbolConverter.toSort(a.typ.substitute(fi.typeVarsMap)))
        val outSort = symbolConverter.toSort(fi.member.typ.substitute(fi.typeVarsMap))
        val id = symbolConverter.toSortSpecificId(fi.member.name, inSorts :+ outSort)
        val fct = terms.Function(id, inSorts, outSort)

        if (!(symbols contains fct)) {
          val functionDecl = terms.FunctionDecl(fct)
          prover.declare(functionDecl)

          if (fi.member.unique) {
            assert(fi.member.formalArgs.isEmpty,
              s"Expected unique domain functions to not take arguments, but found ${fi.member}")

            uniqueFunctions += fct
          }

          symbols += fct
        }
      })
    }

    if (uniqueFunctions.nonEmpty) {
      prover.logComment("Unique domain constants")
      prover.assume(terms.Distinct(uniqueFunctions))
    }

    /* Declare axioms only after all types and functions have been declared. */

    var emittedAxioms = Set[Term]()

    members.foreach{case (domain, memberInstances) =>
      assert(memberInstances forall (_.isConcrete), "Expected only concrete domain member instances")

      val axiomInstances = memberInstances collect {case dai: DomainAxiomInstance => dai}

      prover.logComment("Axioms of " + DomainPrettyPrinter.show(domain))

      axiomInstances.foreach(ai => {
        //        decider.prover.logComment("Axiom " + ai.member.name + ai.typeVarsMap.mkString("[",",","]"))
        val tAx = domainTranslator.translateAxiom(ai.member, ai.typeVarsMap)

        if (!(emittedAxioms contains tAx)) {
          prover.assume(tAx)
          emittedAxioms += tAx
        }
      })
    }
  }

  private def domainMembers(domain: Domain): Map[DomainMember, Domain] =
    (domain.functions.map((_, domain)) ++ domain.axioms.map((_, domain))).toMap

  private def domainMembers(program: Program): Map[DomainMember, Domain] =
    program.domains.flatMap(domainMembers).toMap

  /**
   * Returns the set of concrete domain types that are used in the given program.
   * @param program A program
   * @return The set of concrete domain types that are used in the given program. For all `dt` in
   *         the returned set, `dt.isConcrete` holds.
   */
  private def collectConcreteDomainTypes(program: Program): Set[DomainType] = {
    var domains: Set[DomainType] = Set()
    var newDomains: Set[DomainType] = Set()

    var ds: Iterable[DomainType] = program.domains filter (_.typVars.isEmpty) map (DomainType(_, Map.empty))
//    println("Domain types w/o type variables")
//    ds foreach (dt => println("  " + toStringDT(dt)))
    domains ++= ds

    ds = collectConcreteDomainTypes(program, Map())
//    println("Domain types w/o additional substitution")
//    ds foreach (dt => println("  " + toStringDT(dt)))
    domains ++= ds

    newDomains = domains
    var continue = newDomains.nonEmpty

    while (continue) {
      newDomains = newDomains flatMap (dt => collectConcreteDomainTypes(dt.domain, dt.typVarsMap))

      newDomains = newDomains -- domains
      continue = newDomains.nonEmpty
//      println("Domain types fix-point iteration")
//      newDomains foreach (dt => println(toStringDT(dt)))

      domains ++= newDomains
    }

    domains
  }

  private def collectConcreteDomainTypes(node: Node, typeVarsMap: Map[TypeVar, Type])
                                        : Set[DomainType] = {

    var domains: Set[DomainType] = Set()

    node visit {
      case t: Typed => t.typ match {
        case dt: DomainType =>
          val substitutedDt = dt.substitute(typeVarsMap)
          if (substitutedDt.isConcrete) domains += substitutedDt

        case _ => /* Ignore other types */
      }
    }

    domains
  }

  private def collectConcreteDomainMemberInstances(program: Program, concreteDomainTypes: Set[DomainType])
                                                  : Map[Domain, Set[DomainMemberInstance]] = {

    val membersWithSource = domainMembers(program)

    val instances = InstanceCollection.empty
    var newInstances = InstanceCollection.empty

    /* Get member instances from concrete domain types. */
    insert(
      instances,
      concreteDomainTypes map {case dt =>
        val members: MSet[DomainMemberInstance] =
          MSet((dt.domain.functions.map(DomainFunctionInstance(_, dt.typVarsMap))
                ++ dt.domain.axioms.map(DomainAxiomInstance(_, dt.typVarsMap))
               ):_*)

        (dt.domain, members)})

    /* Get member instances from the program. Since the passed type variable mapping is empty,
     * this will only collect domain functions from domain function applications in which all
     * type variables are instantiated with concrete types. This is always the case for domain
     * function applications that occur in program expressions and program assertions because
     * there cannot be any type variables in those contexts, but it is not necessarily the case
     * for domain function applications that occur inside domain declarations.
     */
    insert(newInstances,
           collectConcreteDomainMemberInstances(program, Map[TypeVar, Type](), membersWithSource))

//    println("\n[collectConcreteDomainMemberInstances]")
//    println("from concrete domain types")
//    printIC(instances)
//    println("from the program without any type var subst")
//    printIC(diff(newInstances, instances))

    insert(instances, newInstances)

    var continue = newInstances.nonEmpty

    while (continue) {
      val nextNewInstances = InstanceCollection.empty

      newInstances foreach {case (domain, memberInstances) =>
        memberInstances foreach {instance =>
          val ms =
            collectConcreteDomainMemberInstances(membersWithSource(instance.member),
                                                 instance.typeVarsMap,
                                                 membersWithSource)

          insert(nextNewInstances, ms)
      }}

      continue = false
      nextNewInstances foreach {case (domain, memberInstances) =>
        memberInstances foreach {instance =>
          if (!instances.entryExists(domain, _ == instance)) continue = true}}

//      println("from a fix-point iteration")
//      println("  continue? " + continue)
//      printIC(diff(nextNewInstances, instances))

      newInstances = nextNewInstances
      insert(instances, newInstances)
    }

    (instances mapValues { _.toSet }).toMap[Domain, Set[DomainMemberInstance]]
  }

  private def collectConcreteDomainMemberInstances(node: Node,
                                                   typeVarsMap: Map[TypeVar, Type],
                                                   membersWithSource: Map[DomainMember, Domain])
                                                  : InstanceCollection = {

    assert(typeVarsMap.values forall (_.isConcrete), "Expected type variable mapping to only map to concrete types")

    val instances = InstanceCollection.empty

    node visit {
      case dfa: DomainFuncApp =>
        val combinedTypeVarsMap = typeVarsMap ++ dfa.typVarMap

        if (dfa.func.freeTypeVariables forall (v => combinedTypeVarsMap.contains(v) && combinedTypeVarsMap(v).isConcrete)) {
          instances.addBinding(membersWithSource(dfa.func), DomainFunctionInstance(dfa.func, combinedTypeVarsMap))
        }

      case df: DomainFunc if df.freeTypeVariables forall typeVarsMap.contains =>
        instances.addBinding(membersWithSource(df), DomainFunctionInstance(df, typeVarsMap))

      case da: DomainAxiom if da.freeTypeVariables forall typeVarsMap.contains =>
        instances.addBinding(membersWithSource(da), DomainAxiomInstance(da, typeVarsMap))
    }

    instances
  }

  /*
   * Internal declarations
   */

  private sealed trait DomainMemberInstance {
    def member: DomainMember
    def typeVarsMap: Map[TypeVar, Type]

    lazy val typeVars = member.freeTypeVariables
    lazy val isConcrete = typeVars forall typeVarsMap.contains

    override lazy val toString = s"$member where $typeVarsMap"
  }

  private case class DomainFunctionInstance(member: DomainFunc, typeVarsMap: Map[TypeVar, Type])
    extends DomainMemberInstance

  private case class DomainAxiomInstance(member: DomainAxiom, typeVarsMap: Map[TypeVar, Type])
    extends DomainMemberInstance

  private type InstanceCollection =
    MHashMap[Domain, MSet[DomainMemberInstance]] with MMultiMap[Domain, DomainMemberInstance]

  private object InstanceCollection {
    def empty: InstanceCollection =
      new MHashMap[Domain, MSet[DomainMemberInstance]] with MMultiMap[Domain, DomainMemberInstance]
  }

  private def insert(into: InstanceCollection, from: Iterable[(Domain, Iterable[DomainMemberInstance])]) {
    from foreach {case (domain, memberInstances) =>
      memberInstances foreach (into.addBinding(domain, _))
    }
  }

  /* For debugging purposes, please don't remove. */

  private def show(ic: Iterable[(Domain, Iterable[DomainMemberInstance])]) {
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
  def show(d: Domain) = d.name + d.typVars.mkString("[",",","]")

  def show(dt: DomainType) =
    dt.domain.name + dt.domain.typVars.mkString("[",",","]") + " where " + dt.typVarsMap
}

trait DomainTranslator[R] {
  def translateAxiom(ax: DomainAxiom, typeVarMap: Map[ast.TypeVar, ast.Type]): R
}

class DefaultDomainTranslator(symbolConverter: SymbolConvert) extends DomainTranslator[Term] {
  def translateAxiom(ax: DomainAxiom, typeVarMap: Map[ast.TypeVar, ast.Type]): Term =
    translateExp((t: ast.Type) => symbolConverter.toSort(t.substitute(typeVarMap)))(ax.exp)

  /**
    *
    * @param toSort
    * @param exp
    * @return
    *
    * TODO: Shares a lot of code with DefaultEvaluator. Reuse!
    */
  private def translateExp(toSort: ast.Type => terms.Sort)(exp: ast.Expression): Term = {
    val f = translateExp(toSort) _

    exp match {
      case q @ ast.Quantified(qvars, body) =>
        val quantifier = q match {
          case _: ast.Forall => terms.Forall
          case _: ast.Exists => terms.Exists
        }
        terms.Quantification(quantifier, qvars map (v => terms.Var(v.name, toSort(v.typ))), f(body))

      case ast.True() => terms.True()
      case ast.False() => terms.False()
      case ast.Not(e0) => terms.Not(f(e0))
      case ast.And(e0, e1) => terms.And(f(e0), f(e1))
      case ast.Or(e0, e1) => terms.Or(f(e0), f(e1))
      case ast.Implies(e0, e1) => terms.Implies(f(e0), f(e1))
      case ast.Ite(e0, e1, e2) => terms.Ite(f(e0), f(e1), f(e2))

      case ast.Equals(e0, e1) => terms.TermEq(f(e0), f(e1))
      case ast.Unequals(e0, e1) => terms.Not(terms.TermEq(f(e0), f(e1)))

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

      case v: ast.Variable => terms.Var(v.name, toSort(v.typ))

      case ast.DomainFuncApp(func, args, typeVarMap) =>
        /* TODO: Is it safe to ignore the typeVarMap when translating the args? */
        val tArgs = args map f
        val inSorts = tArgs map (_.sort)
        val outSort = toSort(exp.typ)
        val id = symbolConverter.toSortSpecificId(func.name, inSorts :+ outSort)
        val df = terms.Function(id, inSorts, outSort)
        terms.DomainFApp(df, tArgs)

      case _: ast.FullPerm => terms.FullPerm()
      case _: ast.NoPerm => terms.NoPerm()
      case ast.FractionalPerm(e0, e1) => terms.FractionPerm(terms.TermPerm(f(e0)), terms.TermPerm(f(e1)))
      case _: ast.EpsilonPerm => terms.EpsilonPerm()

      case _: ast.WildcardPerm => ???
      /* TODO: Would it be sufficient to define a perm-typed 0 < v < write in the preamble and use that here?
       *       It in general doesn't seem to be very useful to use wildcards in domains, but who knows.
       */

      case ast.PermPlus(e0, e1) => terms.PermPlus(terms.TermPerm(f(e0)), terms.TermPerm(f(e1)))
      case ast.PermMinus(e0, e1) => terms.PermMinus(terms.TermPerm(f(e0)), terms.TermPerm(f(e1)))
      case ast.PermTimes(e0, e1) => terms.PermTimes(terms.TermPerm(f(e0)), terms.TermPerm(f(e1)))
      case ast.IntPermTimes(e0, e1) => terms.IntPermTimes(f(e0), terms.TermPerm(f(e1)))
      case ast.PermLE(e0, e1) => terms.AtMost(f(e0), f(e1))
      case ast.PermLT(e0, e1) => terms.Less(f(e0), f(e1))
      case ast.PermGE(e0, e1) => terms.AtLeast(f(e0), f(e1))
      case ast.PermGT(e0, e1) => terms.Greater(f(e0), f(e1))

      case _: sil.ast.SeqExp => ???

      case   _: ast.MemoryLocation | _: ast.AccessPredicate | _: ast.Old | _: ast.FractionalPerm
           | _: ast.ResultLiteral | _: ast.Unfolding | _: ast.InhaleExhaleExp | _: ast.PredicateLocation
           | _: ast.FuncApp | _: ast.CurrentPerm =>

        sys.error(s"Found unexpected expression $exp (${exp.getClass.getName}})")
    }
  }
}
