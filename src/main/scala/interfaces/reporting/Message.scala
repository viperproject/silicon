package semper
package silicon
package interfaces.reporting

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
	
	def loc: ast.SourceLocation
	def reason: Option[Reason]
	def details: Seq[Any]
	
	/* Builder-style setters */
	def at(loc: ast.SourceLocation): Message
	def withDetails(details: Any*): Message	
	def dueTo(reason: Reason): Message
	
	def format: String
}