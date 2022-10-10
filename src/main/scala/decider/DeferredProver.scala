package viper.silicon.decider

import com.typesafe.scalalogging.Logger
import viper.silicon
import viper.silicon.{Config, utils}
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.common.config
import viper.silicon.interfaces.VerificationResult
import viper.silicon.interfaces.decider.{Prover, Result, Unknown}
import viper.silicon.reporting.StateFormatter
import viper.silicon.rules.{StateConsolidationRules, evaluator}
import viper.silicon.state.{DefaultSymbolConverter, IdentifierFactory, State, SymbolConverter, terms}
import viper.silicon.state.terms.{AxiomRewriter, Decl, Fun, FunctionDecl, MacroDecl, Sort, Term, TriggerGenerator, Var}
import viper.silicon.supporters.{QuantifierSupporter, SnapshotSupporter}
import viper.silicon.verifier.{VerificationPoolManager, Verifier}
import viper.silver.ast.{AbstractLocalVar, Exp}
import viper.silver.frontend.FrontendStateCache
import viper.silver.parser.{FastParser, NameAnalyser, PPrimitiv, Resolver, Translator, TypeChecker}
import viper.silver.reporter.Reporter
import viper.silver.verifier.Model

import scala.io.StdIn.readLine
import scala.collection.mutable


case class ProofObligation(id: Int,
                           s: Option[State],
                           decls: Seq[Either[Decl, Iterable[String]]],
                           assumptions: Set[(Seq[Term], Option[String])],
                           assertion: Term,
                           error: Option[Boolean => VerificationResult],
                           pred: Option[Int])


case class NoopDecider() extends Decider {
  override def prover: Prover = ???

  override def pcs: PathConditionStack = null

  override def pushScope(): Unit = {}

  override def popScope(): Unit = {}

  override def checkSmoke(): Boolean = ???

  override def setCurrentBranchCondition(t: Term, te: Option[Exp]): Unit = ???

  override def setPathConditionMark(): Mark = 0

  override def assume(t: Term, description: Option[String]): Unit = ???

  override def assume(ts: InsertionOrderedSet[Term], description: Option[String], enforceAssumption: Boolean): Unit = ???

  override def assume(ts: Iterable[Term], description: Option[String], enforceAssumption: Boolean): Unit = ???

  override def check(t: Term, timeout: Mark): Boolean = ???

  override def assert(t: Term, state: State, timeout: Option[Mark])(Q: Boolean => VerificationResult): VerificationResult = ???

  override def fresh(id: String, sort: Sort): Var = ???

  override def fresh(id: String, argSorts: Seq[Sort], resultSort: Sort): terms.Function = ???

  override def freshMacro(id: String, formalArgs: Seq[Var], body: Term): MacroDecl = ???

  override def fresh(sort: Sort): Var = ???

  override def fresh(v: AbstractLocalVar): Var = ???

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

  override def assert(goal: Term, s: Option[State], timeout: Option[Mark], error: Option[Boolean => VerificationResult] = None): Boolean = {
    // try first, with timeout.
    if (timeout.isDefined && timeout.get != 0) {
      return defaultZ3Prover.assert(goal, s, timeout, error)
    }

    val timeoutResult = defaultZ3Prover.assert(goal, s, Some(DEFAULTTIMEOUT))
    if (timeoutResult)
      return true

    println(s"Obligation number ${assertCounter} with predecessor ${if (oblStack.isEmpty) "NoNE" else oblStack.top.toString}: ${goal}")
    val relevantAssumptions: Set[Assumption] = currentAssumptions.foldLeft(InsertionOrderedSet.empty[Assumption])((s, sp) => s.concat(sp.toSeq))
    proofObligations.append(ProofObligation(assertCounter, s, currentDecls.toSeq, relevantAssumptions, goal, error, Some(oblStack.top)))
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
        println(obl.assertion)
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
    assumptionsInOrder.zipWithIndex.foreach(a => {
      if (!excludedAssumptions.contains(a._2))
        prover.assume(a._1._1)
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
    val evaluated = evaluator.eval3(obl.s.get, translated, null, NoopVerifier())((_, trm, _) => {
      resTerm = trm
      null
    })
    prover.assume(Seq(resTerm), None)
    val timeout = if (proverId == 2) Some(15000) else None
    val res = prover.assert(obl.assertion, None, timeout)
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
