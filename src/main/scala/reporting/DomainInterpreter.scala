package viper.silicon.reporting
import viper.silicon.reporting.{Converter,ExtractedModelEntry}
import viper.silicon.state.terms._
import viper.silicon.state.Identifier
/**
  * the most Generic form of interpreter
  *  @param	E : input type
  *  @param I : info object type
  *  @param	T : result type
  */
trait AbstractInterpreter[E,I,T]{ 
	def interpret(entry:E,info:I):T
}
trait ModelInterpreter[T,I] extends AbstractInterpreter[ExtractedModelEntry,I,T]
trait DomainInterpreter[T,I] extends AbstractInterpreter[DomainValueEntry,I,T]


case class IdentityInterpreter() extends ModelInterpreter[ExtractedModelEntry,Any]{
	def interpret(entry:ExtractedModelEntry,anything:Any):ExtractedModelEntry=entry
}


/**
  * Simple domain interpreter resolves entries in domains recursively otherwise it just returns the value of the entry
  * does not resolve domainvalues stored in sequences or Refs
  * @param c Converter that has all necessary infos about the counterexample domains
  */
case class GenericDomainInterpreter(c:Converter) extends ModelInterpreter[ExtractedModelEntry,Seq[ExtractedModelEntry]]{
	private val domains:Seq[DomainEntry] = c.domains
	private val functions:Seq[ExtractedFunction] = c.non_domain_functions
	def interpret(entry:ExtractedModelEntry,visited:Seq[ExtractedModelEntry]):ExtractedModelEntry ={
		if(visited.contains(entry)){
			entry
		}
		else
		entry match {
			case DomainValueEntry(dom,v) => {
				val allfuncs = functions ++ {val relevantDomain = domains.filter(x=>x.valueName==dom); if(relevantDomain.isEmpty) Nil else relevantDomain.head.functions}
				val relevantFunctions = allfuncs.filter(x=> x.argtypes.length==1 && x.argtypes.head == sorts.UserSort(Identifier.apply(dom)))
				ExtendedDomainValueEntry(DomainValueEntry(dom,v),
											relevantFunctions.map(x=>(x,
															x.apply(Seq(entry))
																			 match{
																				case Right(e)=> e match {
																					 //case va:VarEntry => c.extractVal(va)
																					 case d:DomainValueEntry => interpret(d,entry+:visited)
																					 case x => interpret(x,entry+:visited)
																					} 
																				case _ => OtherEntry(s"${x.fname}","not been able to resolve function")  
																			 } )).toMap
										)	
			}
			case e:VarEntry => interpret(c.extractVal(e),e+:visited)
			case r:RefEntry => RefEntry(r.name,r.fields.map(x=>(x._1,(interpret(x._2._1,r+:visited),x._2._2))))
			case _ => entry
		}
	}
 
}