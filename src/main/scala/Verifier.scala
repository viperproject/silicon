package ch.ethz.inf.pm.silicon

import scala.util.parsing.input.Positional
import scala.collection.Set
import com.weiglewilczek.slf4s.Logging

// import ast.{Member, FieldMember, Method, Function, 
		// Predicate, MonitorInvariant, LockChangeExpr, And, Channel,
		// DebtFreeExpr, ChannelClass}

import silAST.{ASTNode => SILASTNode}
import silAST.expressions.{Expression => SILExpression}
import silAST.expressions.terms.{Term => SILTerm}
import silAST.programs.{Program => SILProgram}
import silAST.programs.symbols.{Function => SILFunction,
    ProgramVariable => SILProgramVariable}
import silAST.methods.implementations.{ /* Statement => SILStatement, */
    BasicBlock => SILBasicBlock, Implementation => SILImplementation}
import silAST.domains.{Domain => SILDomain}

import interfaces.{VerificationResult, Failure, Success, /* MemberVerifier, */
		Producer, Consumer, Executor, Evaluator, /* ProgrammeVerifier, */ MapSupport}
import interfaces.decider.Decider
import interfaces.state.{/* Permission, */ Store, Heap, PathConditions, State, 
		StoreFactory, HeapFactory, PathConditionsFactory, StateFactory, 
		/* PermissionFactory, */ StateFormatter, HeapMerger}
import interfaces.reporting.{Message, Reason}
import interfaces.state.factoryUtils.Ø
// import interfaces.ast.specialVariables
// import interfaces.ast.specialVariables.{This}
// import ast.utils.collections.SetAnd
import state.{/* FractionalPermission, */ TypeConverter}
import state.terms.{Term, Null, FullPerms => Full}
import reporting.ErrorMessages.{ExecutionFailed, NotSupported,
		PostconditionMightNotHold, SpecsMalformed}
import reporting.WarningMessages.{ExcludingUnit}
import reporting.{/* DefaultContext, */ Bookkeeper}

trait AbstractMemberVerifier[ST <: Store[SILProgramVariable, ST],
                             H <: Heap[H], PC <: PathConditions[PC],
                             S <: State[SILProgramVariable, ST, H, S]]
		// extends MemberVerifier
		extends Logging
		with    Evaluator[SILProgramVariable, SILExpression, SILTerm, ST, H, S]
		with    Producer[SILProgramVariable, SILExpression, ST, H, S]
		with    Consumer[SILProgramVariable, SILExpression, ST, H, S]
		with    Executor[SILProgramVariable, SILBasicBlock, ST, H, S] {

	protected val config: Config
		
	protected val decider: Decider[SILProgramVariable, ST, H, PC, S]
	import decider.{fresh, assume}
		
	protected val stateFactory: StateFactory[SILProgramVariable, ST, H, S]
	import stateFactory._
	
	// protected val permissionFactory: PermissionFactory[P]
	// import permissionFactory._

	def verify(node: SILASTNode): VerificationResult = {
		logger.debug("Verify " + node)
		Success()
	}
	
	// def verify(member: Member): VerificationResult = {
		// val success = Success()
		
		// /* TODO: Reset fresh counter here */
		// if (filter(member.fullName)) {
			// logger.warn((ExcludingUnit withDetails(member.fullName)).format)
			// return success
		// }

		// member match {
			// case f: FieldMember => success
			// case m: Method => verify(m)
			// case f: Function => verify(f)
			// case p: Predicate => verify(p)
			// case mi: MonitorInvariant => verify(mi)
		// }
	// }

	def verify(impl: SILImplementation): VerificationResult = {
		logger.debug("\n\n" + "-" * 10 + " IMPLEMENTATION " + impl.method.name + "-" * 10 + "\n")

		decider.prover.logComment(
        "%s %s %s".format("-" * 10, impl.method.name, "-" * 10))

    val ins = impl.method.signature.parameters.variables
    val outs = impl.method.signature.results.variables
    val locals = impl.locals
    // val pre = impl.method.signature.precondition.args
    // val post = impl.method.signature.postcondition.args
    
    // val body = impl.body.startNode.statements

    // println("\n[Verifier/SILImplementation]")
    // println("  succ = " + impl.body.startNode.successors)
    
		val γ = Γ(   ins.map(v => (v, fresh(v)))
							++ outs.map(v => (v, fresh(v)))
							++ locals.map(v => (v, fresh(v))))

		val σ = Σ(γ, Ø, Ø)
		
		val PreErr = SpecsMalformed withDetails(impl.method.name)
		val PostErr = PostconditionMightNotHold
		
    val BigAnd = ast.utils.collections.BigAnd(impl.method.expressionFactory) _
    
		val pre = BigAnd(impl.method.signature.precondition.args, Predef.identity)
		val post = BigAnd(impl.method.signature.postcondition.args, Predef.identity)
											// :: LockChangeExpr(meth.lockchange).setPos(meth.pos)
											// :: Nil)

		/* Combined the well-formedness check and the execution of the body,
		 * which are two separate rules in Smans' paper.
		 */
		// assume(γ(This) ≠ Null(),
			produce(σ, fresh, Full(), pre, PreErr, σ1 => {
				val σ2 = σ1 \ (h = Ø, g = σ1.h)
			 (produce(σ2, fresh, Full(), post, PostErr, _ =>
					Success())
					&&
				// execs(σ1 \ (g = σ1.h), meth.body, ExecutionFailed, σ2 =>
				execn(σ1 \ (g = σ1.h), impl.body.startNode, ExecutionFailed, σ2 =>
					consume(σ2, Full(), post, PostErr, (σ3, _) =>
						// consume(σ3, Full, DebtFreeExpr().setPos(meth.pos), PostErr, (_, _) =>
							Success() /* ) */ )))})
    // )
	}
	
	// def verify(func: Function): VerificationResult = {
		// logger.debug("\n\n" + "-" * 10 + " FUNCTION " + func.id + "-" * 10 + "\n")
		
		// val Result = specialVariables.result(func.out)
		
		// val γ = Γ(    List((This -> fresh(This)),
		                   // (Result -> fresh(Result)))
							// ::: func.ins.map(v => (v, fresh(v))))

		// val σ = Σ(γ, Ø, Ø)
		// // val c = new DefaultContext()
		
		// val PreErr = SpecsMalformed withDetails(func.id)
		// val PostErr = PostconditionMightNotHold

		// /* TODO:
		 // *  - Improve error message in case the ensures-clause is not well-defined
		 // */
		
		// /* Produce includes well-formedness check */
		// assume(γ(This) ≠ Null(),
			// produce(σ, fresh, Full, And(func.pre, func.post), PreErr, _ =>
				// Success())
			// &&
			// produce(σ, fresh, Full, func.pre, PreErr, σ1 =>
				// eval(σ1, func.body, ExecutionFailed, tB =>
					// consume(σ1 \+ (Result, tB), Full, func.post, PostErr, (_, _) =>
						// Success()))))
						// // Success(c4))))
			// //)
	// }

	// def verify(pred: Predicate): VerificationResult = {
		// logger.debug("\n\n" + "-" * 10 + " PREDICATE " + pred.id + "-" * 10 + "\n")
		
		// verifyAssertion(pred.body, pred.fullName)
	// }
	
	// def verify(inv: MonitorInvariant): VerificationResult = {
		// logger.debug("\n\n" + "-" * 10 + " MONITOR INVARIANT " + inv.id + "-" * 10 + "\n")
		
		// verifyAssertion(inv.body, inv.fullName)
	// }
	
	// private def verifyAssertion(a: Expression, id: String): VerificationResult = {
		// val γ = Γ(This -> fresh(This))
		// val σ = Σ(γ, Ø, Ø)
		// // val c = new DefaultContext()
		// val err = SpecsMalformed withDetails(id)
		
		// assume(γ(This) ≠ Null(),
			// produce(σ, fresh, Full, a, err, _ => Success()))
	// }
	
	def filter(str: String): Boolean = (
			 !str.matches(config.includeMembers)
		||  str.matches(config.excludeMembers))
}

class DefaultMemberVerifier[ST <: Store[SILProgramVariable, ST],
														H <: Heap[H], PC <: PathConditions[PC],
														S <: State[SILProgramVariable, ST, H, S]]
		(	val config: Config,
		  val decider: Decider[SILProgramVariable, ST, H, PC, S],
			// val permissionFactory: PermissionFactory[P],
			val stateFactory: StateFactory[SILProgramVariable, ST, H, S],
			val typeConverter: TypeConverter,
			// val mapSupport: MapSupport[ST, H, S],
			// val lockSupport: LockSupport[ST, H, S],
			// val creditSupport: CreditSupport[ST, H, S],
			val chunkFinder: ChunkFinder[H],
			val stateFormatter: StateFormatter[SILProgramVariable, ST, H, S, String],
			val heapMerger: HeapMerger[H],
			val bookkeeper: Bookkeeper)
		extends AbstractMemberVerifier[ST, H, PC, S]
      with  Logging
      with  DefaultEvaluator[ST, H, PC, S]
      with  DefaultProducer[SILProgramVariable, ST, H, PC, S]
      with  DefaultConsumer[SILProgramVariable, ST, H, PC, S]
      with  DefaultExecutor[ST, H, PC, S]
      with  DefaultBrancher[SILProgramVariable, ST, H, PC, S]

class DefaultVerifier[ST <: Store[SILProgramVariable, ST],
                      H <: Heap[H], PC <: PathConditions[PC],
                      S <: State[SILProgramVariable, ST, H, S]]
		(	val config: Config,
			val decider: Decider[SILProgramVariable, ST, H, PC, S],
			// val permissionFactory: PermissionFactory[P],
			val stateFactory: StateFactory[SILProgramVariable, ST, H, S],
			val typeConverter: TypeConverter,
			// val mapSupport: MapSupport[ST, H, S],
			// val lockSupport: LockSupport[ST, H, S],
			// val creditSupport: CreditSupport[ST, H, S],
			val chunkFinder: ChunkFinder[H],
			val stateFormatter: StateFormatter[SILProgramVariable, ST, H, S, String],
			val heapMerger: HeapMerger[H],
			val bookkeeper: Bookkeeper)
		// extends ProgrammeVerifier
			extends Logging {
	
	val mv = new DefaultMemberVerifier[ST, H, PC, S](config, decider, /* permissionFactory, */
																		 stateFactory, typeConverter, /* mapSupport, 
																		 lockSupport, creditSupport, */ chunkFinder, 
																		 stateFormatter, heapMerger, bookkeeper)

	def verify(prog: SILProgram): List[VerificationResult] = {
    // logger.debug("prog = " + prog)
		emitFunctionDeclarations(prog.functions)
    emitDomainDeclarations(prog.domains)
    decider.prover.push()

    var it: Iterator[SILImplementation] =
      prog.methods.flatMap(_.implementations).iterator
    
		/* Verification can be parallelised by forking DefaultMemberVerifiers. */
    var results: List[VerificationResult] = Nil

		if (config.stopOnFirstError) {
			/* Stops on first error */
			while (it.nonEmpty && (results.isEmpty || !results.head.isFatal)) {
				results = mv.verify(it.next) :: results
			}
      
			results = results.reverse
		} else {
			/* Verify members. Verification continues if errors are found, i.e.
			 * all members are verified regardless of previous errors.
			 * However, verification of a single member is aborted on first error.
			 */
			results = it map mv.verify toList
		}

		results
	}
	
	private def emitFunctionDeclarations(fs: Set[SILFunction]) {
    fs.foreach(f =>
      decider.prover.declareSymbol(f.name,
                                   f.signature.parameters.map(p => typeConverter.toSort(p.dataType)),
                                   typeConverter.toSort(f.signature.result.dataType)))
	}
  
	private def emitDomainDeclarations(domains: Set[SILDomain]) {
    val additionalDomains = (domains -- typeConverter.manuallyHandledDomains).filter(_.freeTypeVariables.isEmpty)
    
    additionalDomains.foreach(d => {
      decider.prover.logComment("; Axiomatising " + d.fullName)
      
      decider.prover.declareSort(typeConverter.toSort(d.getType))
      
      d.functions.foreach(f =>
        decider.prover.declareSymbol(f.fullName,
                                     f.signature.parameterTypes.map(typeConverter.toSort),
                                     typeConverter.toSort(f.signature.resultType)))
    })
	}
	
	// def verify(decl: TopLevelDecl): List[VerificationResult] = decl match {
		// case cl: Class =>
			// mv.thisClass = cl
			// verify(cl)
			
		// case ch: Channel =>
			// mv.thisClass = ChannelClass(ch)
			// verify(ch)
	// }
	
	// def verify(clss: Class): List[VerificationResult] = {
		// var results: List[VerificationResult] = Nil
		
		// logger.debug("\n\n" + "-" * 10 + " Class " + clss.id + "-" * 10 + "\n")
		
		// /* Verification can be parallelised by forking DefaultMemberVerifiers. */
		
		// if (config.stopOnFirstError) {
			// /* Stops on first error */
			// var it = clss.members.iterator
			// while (it.nonEmpty && (results.isEmpty || !results.head.isFatal)) {
				// results = mv.verify(it.next) :: results
			// }
			// results = results.reverse
		// } else {
			// /* Verify members. Verification continues if errors are found, i.e.
			 // * all members are verified regardless of previous errors.
			 // * However, verification of a single member is aborted on first error!
			 // */
			// results = clss.members map mv.verify /* Continues */
		// }
		
		// results
	// }
	
	// def verify(ch: Channel): List[VerificationResult] = {
		// logger.debug("\n\n" + "-" * 10 + " CHANNEL " + ch.id + "-" * 10 + "\n")
		
		// if (mv.filter(ch.id)) {
			// logger.warn((ExcludingUnit withDetails(ch.id)).format)
			// return Success() :: Nil
		// }
		
		// import stateFactory._
		// import permissionFactory.Full
		// import decider.{fresh, assume}
		// import mv.produce
		
		// val γ = Γ(This -> fresh(This) :: ch.params.map(v => (v, fresh(v))))
		// val σ = Σ(γ, Ø, Ø)
		// // val c = new DefaultContext()
		
		// val err = SpecsMalformed withDetails(ch.id)

		// /* Well-formedness check */
		// val r =
			// assume(γ(This) ≠ Null(),
				// produce(σ, fresh, Full, ch.where, err, _ =>
					// Success()))

		// r :: Nil
	// }
}