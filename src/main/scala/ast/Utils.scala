package ch.ethz.inf.pm.silicon.ast.utils

import silAST.expressions.{
    Expression => SILExpression,
    BinaryExpression => SILBinaryExpression,
    TrueExpression => SILTrue,
    ExpressionFactory => SILExpressionFactory}
import silAST.symbols.logical.{And => SILAnd}
import ch.ethz.inf.pm.silicon
import silicon.utils.collections.mapReduceLeft
	
/* TODO: Have a constructor taking the SILExpressionFactory and returning an
 *       object that defines BigAnd, And, Not etc.
 *    
 */

object collections {
  // var ef: SILExpressionFactory = null
  
  private def createSILAnd(ef: SILExpressionFactory)(e0: SILExpression, e1: SILExpression) =
    ef.makeBinaryExpression(e0.sourceLocation, SILAnd()(e0.sourceLocation), e0, e1)
  
	def BigAnd(ef: SILExpressionFactory)(it: Iterable[SILExpression], f: SILExpression => SILExpression = e => e) =
		mapReduceLeft(it, f, createSILAnd(ef), SILTrue()(silAST.source.noLocation))

	// def BigOr(it: Iterable[SILExpression], f: SILExpression => SILExpression = e => e) =
		// mapReduceLeft(it, f, Or.apply, True())
}