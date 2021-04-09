package viper.silicon.reporting
import viper.silicon.reporting.{Converter,ExtractedModelEntry}
import viper.silicon.state.terms._
import viper.silicon.state.Identifier
trait ModelInterpreter[T]{
	def interpret(entry:ExtractedModelEntry):T
}
case class IdentityInterpreter() extends ModelInterpreter[ExtractedModelEntry]{
	def interpret(entry:ExtractedModelEntry):ExtractedModelEntry=entry
}


/**
  * Simple domain interpreter resolves entries in domains recursively otherwise it just returns the value of the entry
  *	does not resolve domainvalues stored in sequences or Refs
  * @param c Converter that has all necessary infos about the counterexample domains
  */
case class GenericDomainInterpreter(c:Converter,resolveRecurively:Boolean) extends ModelInterpreter[ExtractedModelEntry]{
	private val domains:Seq[DomainEntry] = c.domains
	private val functions:Seq[ExtractedFunction] = c.non_domain_functions
	def interpret(entry: ExtractedModelEntry): ExtractedModelEntry = {
		entry match {
			case DomainValueEntry(dom,v) => {
				val allfuncs = functions ++ {val relevantDomain = domains.filter(x=>x.valueName==dom); if(relevantDomain.isEmpty) Nil else relevantDomain.head.functions}
				val relevantFunctions = allfuncs.filter(x=> x.argtypes.length==1 && x.argtypes.head == sorts.UserSort(Identifier.apply(dom)))
				ExtendedDomainValueEntry(DomainValueEntry(dom,v),
											relevantFunctions.map(x=>(x,
															x.apply(Seq(entry))
																			 match{
																				case Right(e)=> e match {
																					 case va:VarEntry => c.extractVal(va)
																					 case d:DomainValueEntry => interpret(d)
																					 case _ => e
																					} 
																				case _ => OtherEntry(s"${x.fname}","not been able to resolve function")  
																			 } )).toMap
										)	
			}
			case e:VarEntry => c.extractVal(e)
			case _ => entry
		}
	}
}