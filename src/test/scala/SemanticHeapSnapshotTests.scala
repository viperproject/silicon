// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.tests

import java.nio.file.Path

import scala.io.Source

import viper.silver.testing.{LocatedAnnotation, MissingOutput, SilSuite, UnexpectedOutput, AbstractOutput, AnnotatedTestInput, SystemUnderTest}
import viper.silver.verifier.{AbstractError, Verifier, Failure => SilFailure, Success => SilSuccess, VerificationResult => SilVerificationResult}
import viper.silicon.{Silicon, SiliconFrontend, SymbExLogger}
import viper.silver.frontend.DefaultStates
import viper.silver.reporter.NoopReporter
import viper.silver.ast
import viper.silver.ast.utility.{Nodes, Visitor}

import org.scalatest.ConfigMap

import viper.silicon.tests.SiliconTests

class SemanticHeapSnapshotTests extends SiliconTests {
 	
	val fe = new SiliconFrontend(NoopReporter)//SiliconFrontendWithUnitTesting()
	fe.init(new Silicon(NoopReporter))

	def checkExpr(a: ast.Exp): Boolean = Visitor.reduceTree[ast.Exp, Boolean](a, _.subExps)((e, bs) => {
		bs.forall(identity) && (e match {
			case ast.Forall(_, _, qe) => qe.isPure
			case _ => true
		})
	})

	def checkProgram(prog: ast.Program) : Boolean = {
		(prog.functions ++ prog.methods).isEmpty || (prog.functions ++ prog.methods).map(f => f match {
			case ast.Function(_,_,_,pres,posts,body) => {
				(pres ++ posts ++ (body match {
					case None => Seq()
					case Some(a) => Seq(a)
				})).map(a => checkExpr(a)).forall(identity[Boolean])
			}
			case _ => true
		}).forall(identity[Boolean]) &&
		(prog.predicates.isEmpty || prog.predicates.map(p => p match {
			case ast.Predicate(_,_,Some(a)) => checkExpr(a)
			case _ => true
		}).forall(identity[Boolean]))
	}

	override def isTestToBeIncluded(input: AnnotatedTestInput): Boolean = {
		fe.reset(input.files.head)
		
		val pprog = fe.doParsing(Source.fromFile(input.files.head.toString).mkString)

		pprog match {
			case fe.Succ(x) => fe.doSemanticAnalysis(x) match {
				case fe.Succ(x) => fe.doTranslation(x) match {
					case fe.Succ(prog) => checkProgram(prog)
					case fe.Fail(_) => true
				}
				case fe.Fail(_) => true
			}
			case fe.Fail(_) => true
		}

	}

}

