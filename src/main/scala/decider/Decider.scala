package ch.ethz.inf.pm.silicon.decider

import scala.io.Source
import com.weiglewilczek.slf4s.Logging

import silAST.programs.symbols.{Function => SILFunction}
import silAST.programs.symbols.{ProgramVariable => SILProgramVariable}

import ch.ethz.inf.pm.silicon
import silicon.interfaces.{VerificationResult, Warning, Success}
import silicon.interfaces.decider.{Decider, Unsat}
import silicon.interfaces.state.{Store, Heap, PathConditions, State, FieldChunk, 
		PathConditionsFactory, Chunk, PredicateChunk, AccessRestrictedChunk}
import silicon.interfaces.reporting.{Message}
import silicon.state.{FractionalPermission, ConstFraction, TermFraction,
		DefaultFieldChunk, DefaultPredicateChunk,
		FullPerm => Full, EpsPerm => Eps}
import silicon.state.terms 
import silicon.state.terms.{Term, Eq, Not, TermEq, Var, AtLeast, AtMost, Greater, 
		IntLiteral, Mu, Combine, Ite, FApp, Quantification, And, Or, True,
		SortWrapper, LockMode}
// import silicon.ast
import silicon.reporting.WarningMessages.{SmokeDetected}
import silicon.reporting.ErrorMessages.{FractionMightBeNegative,
		FractionMightBeGT100}
// import silicon.LockSupport

class DefaultDecider[ST <: Store[SILProgramVariable, ST], H <: Heap[H],
										 PC <: PathConditions[PC],
                     S <: State[SILProgramVariable, ST, H, S]]
		(	private val pathConditionsFactory: PathConditionsFactory[PC],
			private val config: silicon.Config)
		extends Decider[SILProgramVariable, FractionalPermission, ST, H, PC, S]
			with Logging {

	private type P = FractionalPermission
	
	// var lockSupport: LockSupport[ST, H, S] = null
	
	val prover = new Z3ProverStdIO(config.z3exe, config.z3log)
	// val prover = new Z3ProverAPI("logfile_api.smt2")
	def π = pathConditions.values
	
	private val pathConditions = pathConditionsFactory.Π()
	private val typeConverter = new silicon.state.DefaultTypeConverter()
	private var performSmokeChecks = config.performSmokeChecks

	prover.logComment("-" * 60)
	prover.logComment("Preamble")
	prover.logComment("-" * 60)
	pushPreamble()

	def enableSmokeChecks(enable: Boolean) = performSmokeChecks = enable
	
	def checkSmoke = prover.check() == Unsat
	
	// private def pushPreamble() {
		// prover.loadPreamble("/preamble.smt2")
		// prover.push()
	// }
	
	private def pushPreamble() {    
    // val preambleFile = "../../../../../preamble.smt2"
    // val preambleFile = "/preamble.smt2"
    // val preambleFile = "."
		// val in = Thread.currentThread().getContextClassLoader().getResourceAsStream(preambleFile)
    // println("CCL = " + Thread.currentThread().getContextClassLoader())
    // sys.exit(0)    
    // if (in == null) sys.error("Could not load resource " + preambleFile)
    
		// var lines =
			// Source.fromInputStream(in).getLines.toList.filterNot(s =>
					// s.trim == "" || s.trim.startsWith(";"))

		var lines =
			Source.fromFile(config.preamble).getLines.toList.filterNot(s =>
					s.trim == "" || s.trim.startsWith(";"))

		/* Multi-line assertions are concatenated into a single string and
		 * send to the prover, because prover.write(str) expects Z3 to reply
		 * to 'str' with success/error. But Z3 will only reply anything if 'str'
		 * has been a complete assertion.
		 */
		while (lines.nonEmpty) {
			val part = lines.head :: lines.tail.takeWhile(l =>
						l.startsWith("\t") || l.startsWith("  "))

			lines = lines.drop(part.size)
			prover.write(part.mkString("\n"))
		}		

		prover.push()
	}

	def assert(t: Term) = {
		val asserted =
			if (t.isInstanceOf[Eq]) {
				/* Simple check to see if 't0 == t0' is to be asserted. */
				val tEq = t.asInstanceOf[Eq]
				tEq.p0 == tEq.p1
			} else
				false

		asserted || π.exists(_ == t) || prover.assert(t)
	}

	def isAsPermissive(perm: P, other: P) =
		/* TODO:
		 * Since assertReadAccess is only true for positive fractions, the
		 * following fails:
		 *   isAsPermissive(_, (8, -2), (8, -4)).
		 * But intuitively, I'd say that (8, -2) > (8, -4), so isAsPermissive
		 * should return true.
		 * This shouldn't be a problem, however, because preconditions can't
		 * require negative epsilon permissions, thus 'other' should never be 
		 * negative. Still ...
		 */

		assertReadAccess((perm - other) + ConstFraction(0, 1))
			/* Without the additional epsilon isAsPermissive would return false
			 * if perm == other because assertReadAccess returns false for zero 
			 * permissions.
			 */
	
	def assertReadAccess(perm: P) = perm match {
		case ConstFraction(per, eps) => per > 0 || (per == 0 && eps > 0)

		case TermFraction(per, eps) =>
			// logger.debug("[assertReadAccess] perm = " + perm)
			val zero = IntLiteral(0)
			assert(Or(Greater(per, zero),
								And(TermEq(per, zero), Greater(eps, zero))))
	}

	def assertNoAccess(perm: P) = perm match {
		case ConstFraction(per, eps) => per == 0 && eps <= 0

		case TermFraction(per, eps) =>
			// logger.debug("[assertNoAccess] perm = " + perm)
			val zero = IntLiteral(0)
			assert(And(TermEq(per, zero), AtMost(eps, zero)))
	}

	def assertWriteAccess(perm: P) = perm match {
		case ConstFraction(per, eps) => per >= 100 && eps >= 0

		case TermFraction(per, eps) =>
			// logger.debug("[assertWriteAccess] perm = " + perm)
			assert(And(AtLeast(per, IntLiteral(100)),
								 AtLeast(eps, IntLiteral(0))))
	}
	
	def assertReadAccess(h: H, rcvr: Term, id: String): Boolean =
		getChunk(h, rcvr, id) match {
			case Some(c: AccessRestrictedChunk[P, _]) => assertReadAccess(c.perm)
			case None => false
		}
	
	def assertWriteAccess(h: H, rcvr: Term, id: String): Boolean =
		getChunk(h, rcvr, id) match {
			case Some(c: AccessRestrictedChunk[P, _]) => assertWriteAccess(c.perm)
			case None => false
		}

	def isNonNegativeFraction(perm: P) = perm match {
		case ConstFraction(per, eps) => per >= 0 && eps >= 0

		case TermFraction(per, eps) =>
			assert(And(AtLeast(per, IntLiteral(0)),
								 AtLeast(eps, IntLiteral(0))))
	}

	/* TODO: Extract isGT100(σ, perm) and implement isValidFraction based on
	 *       isGT100 and isNonNegativeFraction.
	 */
	def isValidFraction(perm: P) = perm match {
		case ConstFraction(per, eps) =>
			if (per < 0 || eps < 0)
				Some(FractionMightBeNegative)
			else if (per > 100)
				Some(FractionMightBeGT100)
			else
				None

		case TermFraction(per, eps) =>
			// logger.debug("[Decider.isValidFraction] perm = " + perm)
			if (!assert(And(AtLeast(per, IntLiteral(0)),
									    AtLeast(eps, IntLiteral(0)))))
				Some(FractionMightBeNegative)
			else if (!assert(AtMost(per, IntLiteral(100))))
				Some(FractionMightBeGT100)
			else
				None
	}

	private def prover_assume(term: Term) = prover.assume(term)
	
	def assume(term: Term, Q: => VerificationResult) =
		assume(Set(term), Q)
	
	/* TODO: CRITICAL!
	 * pathConditions are used as if they are guaranteed to be mutable, e.g.
	 *   pathConditions.pushScope()
	 * instead of
	 *   pathConditions = pathConditions.pushScope()
	 * but the interface does NOT guarantee mutability!
	 */
	
	def assume(_terms: Set[Term], Q: => VerificationResult) = {
		var terms: Set[Term] = _terms
		terms = terms.filterNot(_ == True)    /* Remove True() */
		terms = terms.filterNot(π contains _) /* Remove known assumptions */

		/* Handling an empty set of terms in a distinct case avoids pushing and
		 * popping unnecessary Z3 scopes. This probably does not gain performance,
		 * but avoids cluttering the log file and thus facilitates debugging.
		 */
		if (terms.isEmpty)
			Q
		else {
			pathConditions.pushScope() /* Open a new Syxc-managed path condition scope */
			prover.push() /* Open new prover scope */

			val smokeWarning =
				if (performSmokeChecks)
					assumeWithSmokeChecks(terms)
				else
					assumeWithoutSmokeChecks(terms)
			
			val r =
				smokeWarning match {
					case None => Q
					case Some(w) => w
				}
			
			prover.pop()
			pathConditions.popScope()

			r
		}
	}
	
	private def assumeWithoutSmokeChecks(terms: Set[Term]) = {
		terms foreach pathConditions.push
			/* Add terms to Syxc-managed path conditions */
		terms foreach prover_assume
			/* Add terms to the prover's assumptions */
		None
	}
	
	private def assumeWithSmokeChecks(terms: Set[Term]) = {
		var r: Option[VerificationResult] = None
		val it = terms.iterator
		var assumed: Set[Term] = Set()
		
		while (r == None && it.hasNext) {
			val t = it.next()

			pathConditions.push(t)
			prover_assume(t)
			
			if (checkSmoke) {
				val warning = Warning(SmokeDetected withDetails(t) at t.srcPos)
				logger.error("\n" + warning.message.format)
				logger.error("srcNode = " + t.srcNode)
				logger.error("srcPos = " + t.srcPos + "\n")
				// logger.error("π = " + π)
				r = Some(warning)
			}
		}
		
		r
	}

	def emitFunctionDeclaration(f: SILFunction) = prover.declare(f)

	/* TODO: Have TermConverter declare a default sort */
	def fresh = prover.fresh("$t", terms.IntSort)
  
	def fresh(id: String) = prover.fresh(id, terms.IntSort)
  
	def fresh(v: SILProgramVariable) =
    prover.fresh(v.name, typeConverter.toSort(v.dataType))
	
	def getChunk(h: H, rcvr: Term, id: String) =
		getChunk(h, h.values filter (c => c.id == id), rcvr)
		
	/* TODO:
	 *  - Use PermissionFactory instead of Full/Eps
	 *  - Use ChunkFactory instead of DefaultPredicateChunk/DefaultFieldChunk
	 */
	
	def getFieldChunk(h: H, rcvr: Term, id: String) = {
		val fields = h.values collect {case c: FieldChunk[P] if c.id == id => c}

		getChunk(h, fields, rcvr)
	}
	
	def getPredicateChunk(h: H, rcvr: Term, id: String) = {
		val predicates =
			h.values collect {case c: PredicateChunk[P] if c.id == id => c}

		getChunk(h, predicates, rcvr)
	}
	
	/* The difference between caching and not caching runs in terms of the number
	 * of prover assertions seems to be marginal and probably is not worth
	 * the overhead.
	 *  - chalice/iterator 1144 vs 1147
	 *  - chalice/iterator2 88 vs 75
	 *  - syxc/linked_list 314 vs 314
	 *  - chalice/producer-consumer 116 vs 114 (interesting!)
	 *  - chalice/dining-philosophers 151 vs 151
	 */
	
	/* ATTENTION:
	 * 
	 * Caching does currently not work in all cases!
	 * Problems occur when executing if-statements, specifically when
	 * executing the else-branch after backtracking from the if-branch.
	 *
	 * The problem is as follows:
	 *  - let cache c after if-branch be such that c(t') == t, because
	 *    while executing the if-branch t == t' in π and t.x -> tx in h
	 *  - while executing the if-branch t == t' is NOT in π and t'.x -> tx is in h
	 *    if c has not been reset, finding t'.x in h will fail since c(t') == t
	 *    but t.x is not in h
	 *
	 * Solution: Cache entries must also be pushed/popped
	 */
	
	// private var cache: Map[Term, Term] = Map()
	
	/* Caching version */
	// private def getChunk[C <: Chunk](h: H, chunks: Iterable[C], rcvr: Term) = {
		// val result = findChunk(h, chunks, cache.getOrElse(rcvr, rcvr))
		// if (result.isDefined) cache = cache.updated(rcvr, result.get.rcvr)
		// result
	// }
	
	/* Non-caching version */
	private def getChunk[C <: Chunk](h: H, chunks: Iterable[C], rcvr: Term) =
		findChunk(h, chunks, rcvr)

	private def findChunk[C <: Chunk](h: H, chunks: Iterable[C], rcvr: Term) = (
					 findChunkLiterally(chunks, rcvr)
		orElse findChunkWithProver(h, chunks, rcvr))
	
	private def findChunkLiterally[C <: Chunk](chunks: Iterable[C], rcvr: Term) =
		chunks find (c => c.rcvr == rcvr)
		
	private def findChunkWithProver[C <: Chunk](h: H, chunks: Iterable[C],
																							rcvr: Term): Option[C] = {

		// prover.logComment("Chunk lookup ...")
		// prover.enableLoggingComments(false)
		val chunk = chunks find (c => assert(c.rcvr ≡ rcvr))
		// prover.enableLoggingComments(true)

		chunk
	}
}