package viper.silicon.decider

import com.typesafe.scalalogging.Logger
import viper.silicon
import viper.silicon.{Config, utils}
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.common.config
import viper.silicon.interfaces.{Success, VerificationResult}
import viper.silicon.interfaces.decider.{Prover, Result, Unknown, Unsat}
import viper.silicon.reporting.Converter.symbolConverter
import viper.silicon.reporting.StateFormatter
import viper.silicon.rules.{StateConsolidationRules, evaluator}
import viper.silicon.state.{DefaultSymbolConverter, IdentifierFactory, State, SymbolConverter, terms}
import viper.silicon.state.terms.{AxiomRewriter, Decl, DomainFun, Fun, FunctionDecl, HeapDepFun, IsReadPermVar, MacroDecl, Sort, Term, TriggerGenerator, Var, sorts}
import viper.silicon.supporters.{QuantifierSupporter, SnapshotSupporter}
import viper.silicon.utils.Counter
import viper.silicon.verifier.{VerificationPoolManager, Verifier}
import viper.silver.ast
import viper.silver.frontend.FrontendStateCache
import viper.silver.parser.{FastParser, NameAnalyser, PPrimitiv, Resolver, Translator, TypeChecker}
import viper.silver.reporter.Reporter
import viper.silver.verifier.{ErrorReason, Model, NullPartialVerificationError, PartialVerificationError}
import viper.silver.verifier.errors.{CallFailed, ContractNotWellformed}

import scala.io.StdIn.readLine
import scala.collection.mutable
import scala.reflect.{ClassTag, classTag}


case class ProofObligation(id: Int,
                           s: Option[State],
                           v: Option[Verifier],
                           decls: Seq[Either[Decl, Iterable[String]]],
                           assumptions: Set[(Seq[Term], Option[String])],
                           assertion: Term,
                           eAssertion: Option[ast.Exp],
                           error: Option[Boolean => VerificationResult],
                           pred: Option[Int])


case class NoopDecider() extends Decider {
  override def prover: Prover = ???

  override def pcs: PathConditionStack = null

  override def pushScope(): Unit = {}

  override def popScope(): Unit = {}

  override def checkSmoke(): Boolean = ???

  override def setCurrentBranchCondition(t: Term, te: Option[ast.Exp]): Unit = ???

  override def setPathConditionMark(): Mark = 0

  override def assume(t: Term, description: Option[String]): Unit = ???

  override def assume(ts: InsertionOrderedSet[Term], description: Option[String], enforceAssumption: Boolean): Unit = ???

  override def assume(ts: Iterable[Term], description: Option[String], enforceAssumption: Boolean): Unit = ???

  override def check(t: Term, timeout: Mark): Boolean = ???

  override def assert(t: Term, e: Option[ast.Exp], state: State, v: Verifier, timeout: Option[Mark])(Q: Boolean => VerificationResult): VerificationResult = ???

  override def fresh(id: String, sort: Sort): Var = ???

  override def fresh(id: String, argSorts: Seq[Sort], resultSort: Sort): terms.Function = ???

  override def freshMacro(id: String, formalArgs: Seq[Var], body: Term): MacroDecl = ???

  override def fresh(sort: Sort): Var = ???

  override def fresh(v: ast.AbstractLocalVar): Var = ???

  override def freshARP(id: String): (Var, Term) = ???

  override def appliedFresh(id: String, sort: Sort, appliedArgs: Seq[Term]): terms.App = ???

  override def generateModel(): Unit = ???

  override def getModel(): Model = ???

  override def clearModel(): Unit = ???

  override def hasModel(): Boolean = ???

  override def isModelValid(): Boolean = ???

  override def freshFunctions: InsertionOrderedSet[FunctionDecl] = ???

  override def freshMacros: Vector[MacroDecl] = ???

  override def declareAndRecordAsFreshFunctions(functions: InsertionOrderedSet[FunctionDecl]): Unit = ???

  override def declareAndRecordAsFreshMacros(functions: Vector[MacroDecl]): Unit = ???

  override def setPcs(other: PathConditionStack): Unit = ???

  override def statistics(): silicon.Map[String, String] = ???
}
case class NoopVerifier() extends Verifier {
  override def uniqueId: String = ???

  override def logger: Logger = ???

  override def reporter: Reporter = ???

  override def counter(id: AnyRef): utils.Counter = ???

  override def decider: Decider = NoopDecider()

  val sc = new DefaultSymbolConverter()
  override def symbolConverter: SymbolConverter = sc

  override def stateFormatter: StateFormatter = ???

  override def identifierFactory: IdentifierFactory = ???

  override def triggerGenerator: TriggerGenerator = ???

  override def axiomRewriter: AxiomRewriter = ???

  override def quantifierSupporter: QuantifierSupporter = ???

  override def snapshotSupporter: SnapshotSupporter = ???

  override def stateConsolidator: StateConsolidationRules = ???

  override def verificationPoolManager: VerificationPoolManager = ???
}


case class WrappingVerifier(v: Verifier, d: Decider) extends Verifier{
  override val uniqueId = "asd"

  def logger: Logger = v.logger

  def reporter: Reporter = v.reporter

  def counter(id: AnyRef): Counter = v.counter(id)

  def decider: Decider = d

  def symbolConverter: SymbolConverter = v.symbolConverter

  def stateFormatter: StateFormatter = v.stateFormatter

  def identifierFactory: IdentifierFactory = v.identifierFactory

  def triggerGenerator: TriggerGenerator = v.triggerGenerator

  def axiomRewriter: AxiomRewriter = v.axiomRewriter

  def quantifierSupporter: QuantifierSupporter = v.quantifierSupporter

  def snapshotSupporter: SnapshotSupporter = v.snapshotSupporter

  def stateConsolidator: StateConsolidationRules = v.stateConsolidator

  def verificationPoolManager: VerificationPoolManager = v.verificationPoolManager
}
case class WrappingDecider(p: Prover, pcTerms: Seq[Term]) extends Decider {

  val pathConditions = new LayeredPathConditionStack
  pathConditions.pushScope()
  pcTerms foreach pathConditions.add
  override def prover: Prover = p

  override def pcs = pathConditions

  override def pushScope(): Unit = {
    pathConditions.pushScope()
    p.push()
  }

  override def popScope(): Unit = {
    p.pop()
    pathConditions.popScope()
  }

  override def checkSmoke(): Boolean = p.check(Verifier.config.checkTimeout.toOption) == Unsat

  override def setCurrentBranchCondition(t: Term, te: Option[ast.Exp]): Unit = ???

  override def setPathConditionMark(): Mark = pathConditions.mark()

  override def assume(t: Term, description: Option[String]): Unit = {
    assume(InsertionOrderedSet(Seq(t)), description, false)
  }

  override def assume(ts: InsertionOrderedSet[Term], description: Option[String], enforceAssumption: Boolean): Unit = {
    assumeWithoutSmokeChecks(ts, description)
  }

  override def assume(ts: Iterable[Term], description: Option[String], enforceAssumption: Boolean): Unit = {
    assume(InsertionOrderedSet(ts), description, enforceAssumption)
  }

  private def assumeWithoutSmokeChecks(terms: InsertionOrderedSet[Term], description: Option[String] = None) = {
    /* Add terms to Silicon-managed path conditions */
    terms foreach pathConditions.add

    /* Add terms to the prover's assumptions */
    p.assume(terms.toSeq, description)
    None
  }

  override def check(t: Term, timeout: Mark): Boolean = deciderAssert(t, None, None, None, Some(timeout), None)

  private def deciderAssert(t: Term, e: Option[ast.Exp], s: Option[State], v: Option[Verifier], timeout: Option[Int], Q: Option[Boolean => VerificationResult]) = {
    val result = prover.assert(t, e, s, v, timeout, Q)
    result
  }

  override def assert(t: Term, e: Option[ast.Exp], state: State, v: Verifier, timeout: Option[Mark])(Q: Boolean => VerificationResult): VerificationResult = {
    Q(deciderAssert(t, e, Some(state), Some(v), timeout, Some(Q)))
  }

  override def fresh(id: String, sort: Sort): Var = prover_fresh[Var](id, Nil, sort)

  private def prover_fresh[F <: viper.silicon.state.terms.Function : ClassTag]
  (id: String, argSorts: Seq[Sort], resultSort: Sort)
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
            Var(proverFun.id, proverFun.resultSort).asInstanceOf[F]
          case c if c == classOf[Fun] => proverFun.asInstanceOf[F]
          case c if c == classOf[DomainFun] =>
            DomainFun(proverFun.id, proverFun.argSorts, proverFun.resultSort).asInstanceOf[F]
          case c if c == classOf[HeapDepFun] =>
            HeapDepFun(proverFun.id, proverFun.argSorts, proverFun.resultSort).asInstanceOf[F]
        }


    fun
  }

  override def fresh(id: String, argSorts: Seq[Sort], resultSort: Sort): terms.Function = prover_fresh[Fun](id, argSorts, resultSort)

  override def freshMacro(id: String, formalArgs: Seq[Var], body: Term): MacroDecl = ???

  override def fresh(sort: Sort): Var = prover_fresh[Var]("$t", Nil, sort)

  override def fresh(v: ast.AbstractLocalVar): Var = prover_fresh[Var](v.name, Nil, symbolConverter.toSort(v.typ))

  override def freshARP(id: String): (Var, Term) = {
    val permVar = prover_fresh[Var](id, Nil, sorts.Perm)
    val permVarConstraints = IsReadPermVar(permVar)

    (permVar, permVarConstraints)
  }

  override def appliedFresh(id: String, sort: Sort, appliedArgs: Seq[Term]): terms.App = ???

  override def generateModel(): Unit = ???

  override def getModel(): Model = ???

  override def clearModel(): Unit = ???

  override def hasModel(): Boolean = ???

  override def isModelValid(): Boolean = ???

  override def freshFunctions: InsertionOrderedSet[FunctionDecl] = ???

  override def freshMacros: Vector[MacroDecl] = ???

  override def declareAndRecordAsFreshFunctions(functions: InsertionOrderedSet[FunctionDecl]): Unit = ???

  override def declareAndRecordAsFreshMacros(functions: Vector[MacroDecl]): Unit = ???

  override def setPcs(other: PathConditionStack): Unit = ???

  override def statistics(): silicon.Map[String, String] = ???
}

class DeferredProver(identifierFactory: IdentifierFactory,
                     reporter: Reporter) extends Prover {

  var assertCounter = 0
  var hasBeenEvaluated = false

  type Assumption = (Seq[Term], Option[String])

  val currentDecls = mutable.Queue[Either[Decl, Iterable[String]]]()
  val currentAssumptions = mutable.Stack[mutable.LinkedHashSet[Assumption]]()
  val proofObligations = mutable.ArrayBuffer[ProofObligation]()
  val emittedSettingsString = mutable.Queue[String]()
  val oblStack = mutable.Stack[Int]()

  val defaultTermConverter = new TermToSMTLib2Converter()
  val defaultZ3Prover = new Z3ProverStdIO("deferredDefault", defaultTermConverter, identifierFactory, reporter)

  val DEFAULTTIMEOUT = 1000

  override def assert(goal: Term, e: Option[ast.Exp], s: Option[State], v: Option[Verifier], timeout: Option[Mark], error: Option[Boolean => VerificationResult] = None): Boolean = {
    // try first, with timeout.
    if (timeout.isDefined && timeout.get != 0) {
      return defaultZ3Prover.assert(goal, e, s, v, timeout, error)
    }

    val timeoutResult = defaultZ3Prover.assert(goal, e, s, v, Some(DEFAULTTIMEOUT))
    if (timeoutResult)
      return true

    val goalStr = if (e.isDefined) e.get.toString() else goal.toString
    println(s"Obligation number ${assertCounter} with predecessor ${if (oblStack.isEmpty) "NoNE" else oblStack.top.toString}: ${goalStr}")
    val relevantAssumptions: Set[Assumption] = currentAssumptions.foldLeft(InsertionOrderedSet.empty[Assumption])((s, sp) => s.concat(sp.toSeq))
    proofObligations.append(ProofObligation(assertCounter, s, v, currentDecls.toSeq, relevantAssumptions, goal, e, error, Some(oblStack.top)))
    oblStack.pop
    oblStack.push(assertCounter)
    assertCounter += 1
    true

  }

  override def check(timeout: Option[Mark]): Result = {
    // try w timeout.
    // if success, okay
    // otherwise, just return unknown.
    Unknown
  }

  def checkObligations() : Unit = {

    hasBeenEvaluated = true

    if (proofObligations.size == 0){
      return
    }

    var oblId = -2
    println(s"give me a number less than ${proofObligations.size}. -1 to quit. -2 to iterate through all.")
    oblId = readLine().toInt
    while (oblId != -1){
      println("choose prover. 0 for z3, 1 for cvc5, 2 for trace generating z3.")
      val proverId = readLine().toInt
      if (oblId == -2) {
        for (i <- 0 until proofObligations.size) {
          val obl = proofObligations(i)
          //-println(s"obligation ${i}:")
          evalProofObl(obl, proverId)
        }
      }else{
        val obl = proofObligations(oblId)
        if (obl.eAssertion.isDefined) println(obl.eAssertion.get) else  println(obl.assertion)
        evalProofObl(obl, proverId)
      }

      println(s"give me a number less than ${proofObligations.size}. -1 to quit. -2 to iterate through all.")
      oblId = readLine().toInt
    }
  }

  def evalProofObl(obl: ProofObligation, proverId: Int): Unit = {


    val termConverter = new TermToSMTLib2Converter()
    termConverter.start()
    val prover = if (proverId == 1) {
      val cvcProver = new Cvc5ProverStdIO("CVC5", termConverter, identifierFactory, reporter)
      cvcProver.start()
      new SMTLib2PreambleReader().emitPreamble(Cvc5ProverStdIO.staticPreamble, cvcProver, true)
      cvcProver
    }else if (proverId == 0){
      val z3Prover = new Z3ProverStdIO("Z3", termConverter, identifierFactory, reporter)
      z3Prover.start()
      new SMTLib2PreambleReader().emitPreamble(Z3ProverStdIO.staticPreamble, z3Prover, true)
      z3Prover
    }else{
      val z3Prover = new TraceGeneratingZ3ProverStdIO("Z3", termConverter, identifierFactory, reporter)
      z3Prover.start()
      new SMTLib2PreambleReader().emitPreamble(Z3ProverStdIO.staticPreamble, z3Prover, true)
      z3Prover
    }

    obl.decls.foreach{
      case Left(d) => prover.declare(d)
      case Right(ss) => prover.emit(ss)
    }
    val assumptionsInOrder = obl.assumptions.toSeq.reverse
    assumptionsInOrder.zipWithIndex.foreach(a => {
      println("" + a._2  + ": " + (if (a._1._2.isDefined) a._1._2.get else a._1._1))
    })
    // exclude any ?
    println(s"exclude any assumptions? comma separated list or empty ")
    val excludedAssumptionString = readLine()
    val excludedAssumptions = if (excludedAssumptionString == "") Seq() else excludedAssumptionString.split(",").map(_.trim.toInt).toSeq


    // assume remaining
    var resultingAssumptions: Seq[Term] = Seq()
    assumptionsInOrder.zipWithIndex.foreach(a => {
      if (!excludedAssumptions.contains(a._2)) {
        prover.assume(a._1._1)
        resultingAssumptions ++= a._1._1
      }
    })

    // try adding any?
    println(s"add any assumption? ")
    val added = readLine()
    val fp = new FastParser()
    fp._line_offset = Seq(0, added.length + 1).toArray
    val parsedExp = fastparse.parse(added, fp.exp(_))
    val resolver = FrontendStateCache.resolver
    val pprogram = FrontendStateCache.pprogram
    val pmethod = pprogram.methods.find(_.idndef.name == obl.s.get.member.name)
    resolver.typechecker.curMember = pmethod.get
    val pexp = parsedExp.get.value
    val checkingResult = resolver.typechecker.check(pexp, PPrimitiv("Bool")())
    val translated = FrontendStateCache.translator.exp(pexp)
    var resTerm: Term = null
    val pve: PartialVerificationError = PartialVerificationError(r => ContractNotWellformed(translated, r))
    val evaluated = evaluator.eval3(obl.s.get, translated, pve, WrappingVerifier(obl.v.get, WrappingDecider(prover, resultingAssumptions)))((_, trm, _) => {
      resTerm = trm
      Success()
    })
    evaluated match {
      case Success() =>
        val proved = prover.assert(resTerm, None, None, None, None)
        if (proved) {
          println("correct! assuming now")
          prover.assume(Seq(resTerm), None)
        } else {
          println("nope, couldn't prove that.")
        }
      case _ =>
        println("Error evaluating expression: " + evaluated.toString)
    }


    val timeout = if (proverId == 2) Some(15000) else None
    val res = prover.assert(obl.assertion, None, None, None, timeout)
    if (obl.error.isDefined) {
      if (res) {
        println("all good")
      }else{
        println(obl.error.get(res))
      }
    }else{
      println(s"assert succeeded: ${res}")
    }
    prover.stop()
  }

  override def fresh(idstr: String, argSorts: Seq[Sort], resultSort: Sort): terms.Function = {
    val id = identifierFactory.fresh(idstr)
    val fun = Fun(id, argSorts, resultSort)
    val decl = FunctionDecl(fun)
    currentDecls.append(Left(decl))

    defaultZ3Prover.emit(defaultTermConverter.convert(decl))

    fun
  }

  override def statistics(): silicon.Map[String, String] = ???

  override def clearLastModel(): Unit = {}

  override def name: String = "Deferred Prover"

  override def minVersion: config.Version = Z3ProverStdIO.minVersion

  override def maxVersion: Option[config.Version] = Z3ProverStdIO.maxVersion

  override def version(): config.Version = config.Version("4.5.0")

  override def staticPreamble: String = Z3ProverStdIO.staticPreamble

  override def randomizeSeedsOptions: Seq[String] = Z3ProverStdIO.randomizeSeedsOptions

  override def push(n: Mark): Unit = {
    oblStack.push(oblStack.top)
    currentAssumptions.push(mutable.LinkedHashSet())
    defaultZ3Prover.push(n)
  }

  override def pop(n: Mark): Unit = {
    oblStack.pop
    currentAssumptions.pop
    defaultZ3Prover.pop(n)
  }

  override def reset(): Unit = {
    start()
    stop()
  }

  override def emit(content: String): Unit = {
    currentDecls.append(Right(Seq(content)))
    defaultZ3Prover.emit(content)
  }

  override def emitSettings(contents: Iterable[String]): Unit = {
    // ignore
    defaultZ3Prover.emitSettings(contents)
  }

  override def emit(contents: Iterable[String]): Unit = {
    currentDecls.append(Right(contents))
    defaultZ3Prover.emit(contents)
  }

  override def assume(terms: Seq[Term], description: Option[String] = None): Unit = {
    currentAssumptions.top.add((terms, description))
    defaultZ3Prover.assume(terms, description)
  }

  override def declare(decl: Decl): Unit = {
    currentDecls.append(Left(decl))
    defaultZ3Prover.declare(decl)
  }

  override def comment(content: String): Unit = {
    defaultZ3Prover.comment(content)
  }

  override def saturate(timeout: Mark, comment: String): Unit = {
    defaultZ3Prover.saturate(timeout, comment)
  }

  override def saturate(data: Option[Config.ProverStateSaturationTimeout]): Unit = {
    defaultZ3Prover.saturate(data)
  }

  override def start(): Unit = {
    currentAssumptions.push(mutable.LinkedHashSet())
    oblStack.push(-1)
    defaultTermConverter.start()
    defaultZ3Prover.start()
  }

  override def stop(): Unit = {
    if (hasBeenEvaluated){
      assertCounter = 0
      currentDecls.clear()
      currentAssumptions.clear()
      proofObligations.clear()
      oblStack.clear()
      defaultTermConverter.stop()
      defaultZ3Prover.stop()
    }
  }

  override def hasModel(): Boolean = ???

  override def isModelValid(): Boolean = ???

  override def getModel(): Model = ???

  override def pushPopScopeDepth: Mark = ???
}
