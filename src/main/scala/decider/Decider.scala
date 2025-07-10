// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.decider

import com.typesafe.scalalogging.Logger
import viper.silicon.debugger.DebugExp
import viper.silicon._
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.interfaces._
import viper.silicon.interfaces.decider._
import viper.silicon.logger.records.data.{DeciderAssertRecord, DeciderAssumeRecord, ProverAssertRecord}
import viper.silicon.state._
import viper.silicon.state.terms.{Term, _}
import viper.silicon.utils.ast.{extractPTypeFromExp, simplifyVariableName}
import viper.silicon.verifier.{Verifier, VerifierComponent}
import viper.silver.ast
import viper.silver.ast.{LocalVarWithVersion, NoPosition}
import viper.silver.components.StatefulComponent
import viper.silver.parser.{PKw, PPrimitiv, PReserved, PType}
import viper.silver.reporter.{ConfigurationConfirmation, InternalWarningMessage}
import viper.silver.verifier.{DependencyNotFoundError, Model}

import scala.collection.immutable.HashSet
import scala.reflect.{ClassTag, classTag}
import scala.collection.mutable

/*
 * Interfaces
 */

trait Decider {
  def functionDecls: Set[FunctionDecl]

  def macroDecls: Vector[MacroDecl]
  def prover: Prover
  def setProverOptions(options: Map[String, String]): Unit
  def getProverOptions(): Map[String, String]
  def resetProverOptions(): Unit
  def createProver(proverName: String, userArgsString: Option[String]): Option[DependencyNotFoundError]

  def pcs: PathConditionStack

  def debugVariableTypes: Map[String, PType]

  def pushScope(): Unit
  def popScope(): Unit

  def checkSmoke(isAssert: Boolean = false): Boolean

  def setCurrentBranchCondition(t: Term, te: (ast.Exp, Option[ast.Exp])): Unit
  def setPathConditionMark(): Mark

  def finishDebugSubExp(description : String): Unit

  def startDebugSubExp(): Unit

  def assume(t: Term, e: ast.Exp, finalExp: ast.Exp): Unit
  def assume(t: Term, e: Option[ast.Exp], finalExp: Option[ast.Exp]): Unit
  def assume(t: Term, debugExp: Option[DebugExp]): Unit
  def assume(terms: Seq[Term], debugExps: Option[Seq[DebugExp]]): Unit
  def assumeDefinition(t: Term, debugExp: Option[DebugExp]): Unit
  def assume(assumptions: Iterable[(Term, Option[DebugExp])]): Unit
  def assume(assumptions: InsertionOrderedSet[(Term, Option[DebugExp])], enforceAssumption: Boolean = false, isDefinition: Boolean = false): Unit
  def assume(terms: Iterable[Term], debugExp: Option[DebugExp], enforceAssumption: Boolean): Unit

  def check(t: Term, timeout: Int): Boolean

  /* TODO: Consider changing assert such that
   *         1. It passes State and Operations to the continuation
   *         2. The implementation reacts to a failing assertion by e.g. a state consolidation
   */
  def assert(t: Term, timeout: Option[Int] = None)(Q:  Boolean => VerificationResult): VerificationResult

  def fresh(id: String, sort: Sort, ptype: Option[PType]): Var
  def fresh(id: String, argSorts: Seq[Sort], resultSort: Sort): Function
  def freshMacro(id: String, formalArgs: Seq[Var], body: Term): MacroDecl

  def fresh(sort: Sort, pType: Option[PType]): Var
  def fresh(v: ast.AbstractLocalVar): (Var, Option[ast.LocalVarWithVersion])
  def freshARP(id: String = "$k"): (Var, Term, Option[ast.LocalVarWithVersion])
  def appliedFresh(id: String, sort: Sort, appliedArgs: Seq[Term]): App

  def createAlias(t: Term, s: State): Term

  def generateModel(): Unit
  def getModel(): Model
  def clearModel(): Unit
  def hasModel(): Boolean
  def isModelValid(): Boolean

/* [BRANCH-PARALLELISATION] */
  // HashSets lead to non-deterministic order, but branch parallelization leads to highly non-deterministic prover
  // states anyway (and Scala does not seem to have efficient order-preserving sets). ListSets are significantly
  // slower, so this tradeoff seems worth it.
  def freshFunctions: Set[FunctionDecl]
  def freshMacros: Vector[MacroDecl]
  def declareAndRecordAsFreshFunctions(functions: Set[FunctionDecl]): Unit
  def declareAndRecordAsFreshMacros(functions: Seq[MacroDecl]): Unit
  def setPcs(other: PathConditionStack): Unit

  def statistics(): Map[String, String]
}

/*
 * Implementations
 */

trait DefaultDeciderProvider extends VerifierComponent { this: Verifier =>

  val debugMode: Boolean
  def logger: Logger
  def symbolConverter: SymbolConverter
  def termConverter: TermToSMTLib2Converter
    /* TODO: Bad design: this decider chooses which prover to instantiate,
     *       but relies on another component to provide a suitable TermConverter
     */
  def identifierFactory: IdentifierFactory

  object decider extends Decider with StatefulComponent {
    private var _prover: Prover = _
    private var pathConditions: PathConditionStack = _

    private var _declaredFreshFunctions: Set[FunctionDecl] = _ /* [BRANCH-PARALLELISATION] */
    private var _declaredFreshMacros: Vector[MacroDecl] = _
    private var _declaredFreshMacroNames: Set[String] = _ /* contains names of _declaredFreshMacros for faster lookup */

    private var _proverOptions: Map[String, String] = Map.empty
    private var _proverResetOptions: Map[String, String] = Map.empty
    private val _debuggerAssumedTerms: mutable.Set[Term] = mutable.Set.empty
    
    def functionDecls: Set[FunctionDecl] = _declaredFreshFunctions
    def macroDecls: Vector[MacroDecl] = _declaredFreshMacros

    def prover: Prover = _prover

    def pcs: PathConditionStack = pathConditions

    var debugVariableTypes : Map[String, PType] = Map.empty

    def setPcs(other: PathConditionStack) = {
      /* [BRANCH-PARALLELISATION] */
      pathConditions = other
      while (prover.pushPopScopeDepth > 1){
        prover.pop()
      }
      // TODO: Change interface to make the cast unnecessary?
      val layeredStack = other.asInstanceOf[LayeredPathConditionStack]
      layeredStack.layers.reverse.foreach(l => {
        l.assumptions foreach prover.assume
        prover.push(timeout = Verifier.config.pushTimeout.toOption)
      })
    }

    private def getProver(prover: String): Prover = prover match {
      case Z3ProverStdIO.name => new Z3ProverStdIO(uniqueId, termConverter, identifierFactory, reporter)
      case Cvc5ProverStdIO.name => new Cvc5ProverStdIO(uniqueId, termConverter, identifierFactory, reporter)
      case Z3ProverAPI.name => new Z3ProverAPI(uniqueId, new TermToZ3APIConverter(), identifierFactory, reporter, triggerGenerator)
      case prover =>
        val msg1 = s"Unknown prover '$prover' provided. Defaulting to ${Z3ProverStdIO.name}."
        logger warn msg1
        getProver(Z3ProverStdIO.name)
    }

    def createProver(proverName: String, userArgsString: Option[String]): Option[DependencyNotFoundError] = {
      _prover = getProver(proverName)

      _prover.start(userArgsString) /* Cannot query prover version otherwise */

      val proverVersion = _prover.version()
      // One can pass some options. This allows to check whether they have been received.

      val path = prover match {
        case pio: ProverStdIO => pio.proverPath
        case _ => "No Path"
      }
      val msg = s"Using ${_prover.name} $proverVersion located at ${path}"
      reporter report ConfigurationConfirmation(msg)
      logger debug msg

      if (proverVersion < _prover.minVersion) {
        val msg1 = s"Expected at least ${_prover.name} version ${_prover.minVersion.version}, but found $proverVersion"
        reporter report InternalWarningMessage(msg1)
        logger warn msg1
      }

      if (_prover.maxVersion.fold(false)(_ < proverVersion)) {
        val msg1 = s"Silicon might not work with ${_prover.name} version $proverVersion, consider using ${_prover.maxVersion.get}"
        reporter report InternalWarningMessage(msg1)
        logger warn msg1
      }

      None
    }

    override def setProverOptions(options: Map[String, String]): Unit = {
      _proverOptions = _proverOptions ++ options
      val resetOptions = _proverOptions.map { case (k, v) => (k, _prover.setOption(k, v)) }
      _proverResetOptions = resetOptions ++ _proverResetOptions
    }

    override def getProverOptions(): Map[String, String] = _proverOptions

    override def resetProverOptions(): Unit = {
      _proverResetOptions.foreach { case (k, v) => _prover.setOption(k, v) }
      _proverResetOptions = Map.empty
      _proverOptions = Map.empty
    }

    /* Life cycle */

    def start(): Unit = {
      pathConditions = new LayeredPathConditionStack()
      _declaredFreshFunctions = if (Verifier.config.parallelizeBranches()) HashSet.empty else InsertionOrderedSet.empty /* [BRANCH-PARALLELISATION] */
      _declaredFreshMacros = Vector.empty
      _declaredFreshMacroNames = HashSet.empty
      createProver(Verifier.config.prover(), Verifier.config.proverArgs)
    }

    def reset(): Unit = {
      _prover.reset()
      pathConditions = new LayeredPathConditionStack()
      _declaredFreshFunctions = if (Verifier.config.parallelizeBranches()) HashSet.empty else InsertionOrderedSet.empty /* [BRANCH-PARALLELISATION] */
      _declaredFreshMacros = Vector.empty
      _declaredFreshMacroNames = HashSet.empty
      _proverOptions = Map.empty
    }

    def stop(): Unit = {
      if (_prover != null) _prover.stop()
    }

    /* Assumption scope handling */

    def pushScope(): Unit = {
      //val commentRecord = new CommentRecord("push", null, null)
      //val sepIdentifier = symbExLog.openScope(commentRecord)
      pathConditions.pushScope()
      _prover.push(timeout = Verifier.config.pushTimeout.toOption)
      //symbExLog.closeScope(sepIdentifier)
    }

    def popScope(): Unit = {
      //val commentRecord = new CommentRecord("pop", null, null)
      //val sepIdentifier = symbExLog.openScope(commentRecord)
      _prover.pop()
      pathConditions.popScope()
      //symbExLog.closeScope(sepIdentifier)
    }

    def setCurrentBranchCondition(t: Term, te: (ast.Exp, Option[ast.Exp])): Unit = {
      pathConditions.setCurrentBranchCondition(t, te)
      assume(t, Option.when(te._2.isDefined)(te._1), te._2)
    }

    def setPathConditionMark(): Mark = pathConditions.mark()

    /* Assuming facts */

    def startDebugSubExp(): Unit = {
      if (debugMode) {
        pathConditions.startDebugSubExp()
      }
    }

    def finishDebugSubExp(description: String): Unit = {
      if (debugMode) {
        pathConditions.finishDebugSubExp(description)
      }
    }

    def addDebugExp(e: DebugExp): Unit = {
      if (debugMode) {
        pathConditions.addDebugExp(e)
      }
    }

    def assume(t: Term, e : ast.Exp, finalExp : ast.Exp): Unit = {
      assume(assumptions=InsertionOrderedSet((t, Some(DebugExp.createInstance(e, finalExp)))), false, false)
    }

    def assume(t: Term, e: Option[ast.Exp], finalExp: Option[ast.Exp]): Unit = {
      if (finalExp.isDefined) {
        assume(assumptions=InsertionOrderedSet((t, Some(DebugExp.createInstance(e.get, finalExp.get)))), false, false)
      } else {
        assume(assumptions=InsertionOrderedSet((t, None)), false, false)
      }
    }

    def assume(t: Term, debugExp: Option[DebugExp]): Unit = {
      assume(InsertionOrderedSet(Seq((t, debugExp))), false)
    }

    def assumeDefinition(t: Term, debugExp: Option[DebugExp]): Unit = {
      assume(InsertionOrderedSet(Seq((t, debugExp))), enforceAssumption=false, isDefinition=true)
    }

    def assume(assumptions: Iterable[(Term, Option[DebugExp])]): Unit =
      assume(InsertionOrderedSet(assumptions), false)

    def assume(assumptions: InsertionOrderedSet[(Term, Option[DebugExp])], enforceAssumption: Boolean = false, isDefinition: Boolean = false): Unit = {
      val filteredAssumptions =
        if (enforceAssumption) assumptions
        else assumptions filterNot (a => isKnownToBeTrue(a._1))


      if (debugMode) {
        filteredAssumptions foreach (a => addDebugExp(a._2.get.withTerm(a._1)))
      }

      if (filteredAssumptions.nonEmpty) assumeWithoutSmokeChecks(filteredAssumptions map (_._1), isDefinition=isDefinition)
    }

    def assume(assumptions: Seq[Term], debugExps: Option[Seq[DebugExp]]): Unit = {
      assumeWithoutSmokeChecks(InsertionOrderedSet(assumptions))
      if (debugMode) {
        debugExps.get foreach (e => addDebugExp(e))
      }
    }

    def assume(terms: Iterable[Term], debugExp: Option[DebugExp], enforceAssumption: Boolean): Unit = {
      val filteredTerms =
        if (enforceAssumption) terms
        else terms filterNot isKnownToBeTrue

      if (debugMode && filteredTerms.nonEmpty) {
        addDebugExp(debugExp.get.withTerm(And(filteredTerms)))
      }

      if (filteredTerms.nonEmpty) assumeWithoutSmokeChecks(InsertionOrderedSet(filteredTerms))
    }

    def debuggerAssume(terms: Iterable[Term], de: DebugExp) = {
      terms.foreach(t => {
        if (!_debuggerAssumedTerms.contains(t)) {
          _debuggerAssumedTerms += t
          prover.assume(t)
          //TODODELETEtermSources.put(t, de)
        }
      })
    }

    private def assumeWithoutSmokeChecks(terms: InsertionOrderedSet[Term], isDefinition: Boolean = false) = {
      val assumeRecord = new DeciderAssumeRecord(terms)
      val sepIdentifier = symbExLog.openScope(assumeRecord)

      /* Add terms to Silicon-managed path conditions */
      if (isDefinition) {
        terms foreach pathConditions.addDefinition
      } else {
        terms foreach pathConditions.add
      }

      /* Add terms to the prover's assumptions */
      terms foreach prover.assume

      symbExLog.closeScope(sepIdentifier)
      None
    }

    /* Asserting facts */

    def checkSmoke(isAssert: Boolean = false): Boolean = {
      val timeout = if (isAssert) Verifier.config.assertTimeout.toOption else Verifier.config.checkTimeout.toOption
      prover.check(timeout) == Unsat
    }

    def check(t: Term, timeout: Int): Boolean = deciderAssert(t, Some(timeout))

    def assert(t: Term, timeout: Option[Int] = Verifier.config.assertTimeout.toOption)
              (Q: Boolean => VerificationResult)
              : VerificationResult = {

      val success = deciderAssert(t, timeout)

      // If the SMT query was not successful, store it (possibly "overwriting"
      // any previously saved query), otherwise discard any query we had saved
      // previously (it did not cause a verification failure) and ignore the
      // current one, because it cannot cause a verification error.
      if (success)
        symbExLog.discardSMTQuery()
      else
        symbExLog.setSMTQuery(t)

      Q(success)
    }

    private def deciderAssert(t: Term, timeout: Option[Int]) = {
      val assertRecord = new DeciderAssertRecord(t, timeout)
      val sepIdentifier = symbExLog.openScope(assertRecord)

      val asserted = isKnownToBeTrue(t)
      val result = asserted || proverAssert(t, timeout)

      symbExLog.closeScope(sepIdentifier)
      result
    }

    private def isKnownToBeTrue(t: Term) = t match {
      case True => true
  //    case eq: BuiltinEquals => eq.p0 == eq.p1 /* WARNING: Blocking trivial equalities might hinder axiom triggering. */
      case _ if pcs.assumptions contains t => true
      case q: Quantification if q.body == True => true
      case _ => false
    }

    private def proverAssert(t: Term, timeout: Option[Int]) = {
      val assertRecord = new ProverAssertRecord(t, timeout)
      val sepIdentifier = symbExLog.openScope(assertRecord)

      val result = prover.assert(t, timeout)

      symbExLog.whenEnabled {
        assertRecord.statistics = Some(symbExLog.deltaStatistics(prover.statistics()))
      }

      symbExLog.closeScope(sepIdentifier)

      result
    }

    /* Fresh symbols */

    def fresh(id: String, argSorts: Seq[Sort], resultSort: Sort): Function =
      prover_fresh[Fun](id, argSorts, resultSort, false)

    def fresh(id: String, sort: Sort, pType: Option[PType]): Var = {
      val term = prover_fresh[Var](id, Nil, sort, false)
      if (debugMode) debugVariableTypes += (term.id.name -> pType.get)
      term
    }

    def fresh(s: Sort, pType: Option[PType]): Var = {
      val term = prover_fresh[Var]("$t", Nil, s, false)
      if (debugMode) debugVariableTypes += (term.id.name -> pType.get)
      term
    }

    def fresh(v: ast.AbstractLocalVar): (Var, Option[ast.LocalVarWithVersion]) = {
      val withExp = debugMode
      val term = fresh(v.name, symbolConverter.toSort(v.typ), Option.when(withExp)(extractPTypeFromExp(v)))
      (term, Option.when(withExp)(LocalVarWithVersion(simplifyVariableName(term.id.name), v.typ)(v.pos, v.info, v.errT)))
    }

    def freshARP(id: String = "$k"): (Var, Term, Option[ast.LocalVarWithVersion]) = {
      val permVar = prover_fresh[Var](id, Nil, sorts.Perm, true)
      val permVarConstraints = IsReadPermVar(permVar)
      if (debugMode) debugVariableTypes += (permVar.id.name -> PPrimitiv(PReserved(PKw.Perm)((NoPosition, NoPosition)))())
      (permVar, permVarConstraints, Option.when(debugMode)(LocalVarWithVersion(simplifyVariableName(permVar.id.name), ast.Perm)()))
    }

    def freshMacro(id: String, formalArgs: Seq[Var], body: Term): MacroDecl = {
      val name = identifierFactory.fresh(id)
      val macroDecl = MacroDecl(name, formalArgs, body)

      prover.declare(macroDecl)

      _declaredFreshMacros = _declaredFreshMacros :+ macroDecl /* [BRANCH-PARALLELISATION] */
      _declaredFreshMacroNames = _declaredFreshMacroNames + name.name

      macroDecl
    }

    def appliedFresh(id: String, sort: Sort, appliedArgs: Seq[Term]): App = {
      val appliedSorts = appliedArgs.map(_.sort)
      val func = fresh(id, appliedSorts, sort)

      App(func, appliedArgs)
    }

    private def prover_fresh[F <: Function : ClassTag]
                            (id: String, argSorts: Seq[Sort], resultSort: Sort, isARP: Boolean)
                            : F = {
//      context.bookkeeper.freshSymbols += 1

      val proverFun = prover.fresh(id, argSorts, resultSort)

      val destClass = classTag[F].runtimeClass

      val fun: F =
        if (proverFun.getClass == destClass)
          proverFun.asInstanceOf[F]
        else
          destClass match {
            case c if c == classOf[Var] =>
              Predef.assert(proverFun.argSorts.isEmpty)
              Var(proverFun.id, proverFun.resultSort, isARP).asInstanceOf[F]
            case c if c == classOf[Fun] => proverFun.asInstanceOf[F]
            case c if c == classOf[DomainFun] =>
              DomainFun(proverFun.id, proverFun.argSorts, proverFun.resultSort).asInstanceOf[F]
            case c if c == classOf[HeapDepFun] =>
              HeapDepFun(proverFun.id, proverFun.argSorts, proverFun.resultSort).asInstanceOf[F]
          }

      val decl = FunctionDecl(fun)
      _declaredFreshFunctions = _declaredFreshFunctions + decl /* [BRANCH-PARALLELISATION] */

      fun
    }

    def createAlias(t: Term, s: State): Term = {
      t match {
        case hvr: HasVarRepr if hvr.varRepr.isEmpty && s.quantifiedVariables.isEmpty && s.isMethodVerification =>
          val md = freshMacro("tmpTerm", Seq(), t)
          val mcr = Macro(md.id, Seq(), md.body.sort)
          hvr.varRepr = Some(App(mcr, Seq()))
          t
        case _ => t
      }
    }


/* [BRANCH-PARALLELISATION] */
    def freshFunctions: Set[FunctionDecl] = _declaredFreshFunctions
    def freshMacros: Vector[MacroDecl] = _declaredFreshMacros

    def declareAndRecordAsFreshFunctions(functions: Set[FunctionDecl]): Unit = {
      for (f <- functions) {
        if (!_declaredFreshFunctions.contains(f)) {
          prover.declare(f)
          _declaredFreshFunctions = _declaredFreshFunctions + f
        }
      }
    }

    def declareAndRecordAsFreshMacros(macros: Seq[MacroDecl]): Unit = {
      for (m <- macros) {
        if (!_declaredFreshMacroNames.contains(m.id.name)) {
          prover.declare(m)
          _declaredFreshMacros = _declaredFreshMacros.appended(m)
          _declaredFreshMacroNames = _declaredFreshMacroNames + m.id.name
        }
      }
    }

    /* Misc */

    def statistics(): Map[String, String] = prover.statistics()

    override def generateModel(): Unit = proverAssert(False, Verifier.config.assertTimeout.toOption)

    override def getModel(): Model = prover.getModel()

    override def hasModel(): Boolean = prover.hasModel()

    override def isModelValid(): Boolean = prover.isModelValid()

    override def clearModel(): Unit = prover.clearLastAssert()
  }
}
