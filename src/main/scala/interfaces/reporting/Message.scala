package ch.ethz.inf.pm.silicon.interfaces.reporting

// import scala.util.parsing.input.Position
import silAST.source.{SourceLocation => SILSourceLocation}

trait Categorie {
	def name: String
}

trait Reason {
	def code: Int
	def	text: String
	def format: String
}

trait Message {
	def cat: Categorie
	def code: Int
	def text: String
	
	def loc: SILSourceLocation
	def reason: Option[Reason]
	def details: Seq[Any]
	
	/* Builder-style setters */
	def at(loc: SILSourceLocation): Message
	def withDetails(details: Any*): Message	
	def dueTo(reason: Reason): Message
	
	def format: String
}