package ch.ethz.inf.pm.silicon.ast.utils

import silAST.expressions.{
    Expression => SILExpression,
    BinaryExpression => SILBinaryExpression,
    TrueExpression => SILTrue,
    ExpressionFactory => SILExpressionFactory}
import silAST.symbols.logical.{And => SILAnd}
import silAST.source.{noLocation => SILNoLocation}

import ch.ethz.inf.pm.silicon
import silicon.utils.collections.mapReduceLeft
// import syxc.ast.{Expression, And, Or, True}
	
object collections {
  var ef: SILExpressionFactory = null
  
  private def createSILAnd(e0: SILExpression, e1: SILExpression) =
    ef.makeBinaryExpression(SILNoLocation, SILAnd(), e0, e1)
    // SILBinaryExpression(SILNoLocation, SILAnd(), e0, e1)
  
	def BigAnd(it: Iterable[SILExpression], f: SILExpression => SILExpression = e => e) =
		mapReduceLeft(it, f, createSILAnd, SILTrue())
		
	// def BigOr(it: Iterable[SILExpression], f: SILExpression => SILExpression = e => e) =
		// mapReduceLeft(it, f, Or.apply, True())
}