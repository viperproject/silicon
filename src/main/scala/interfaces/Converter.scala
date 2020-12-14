package viper.silicon.interfaces


import viper.silicon.interfaces.state.Chunk
import viper.silicon.resources.{FieldID, PredicateID}
import viper.silicon.state.{Store, Heap, State, BasicChunk}
import viper.silver.verifier.{Model}
import viper.silicon.state.terms.{Term, Unit, IntLiteral, Null, Var, App, Combine,
                                  First, Second, SortWrapper, PredicateLookup}
import viper.silicon.reporting.SiliconException

/*
sealed trait ExtModelEntry
case class LitIntEntry(value: BigInt) extends ExtModelEntry 
case class LitBoolEntry(value: Boolean) extends ExtModelEntry
case class RefEntry(fields: Map[String, ExtModelEntry]) extends ExtModelEntry
case class VarEntry(name: String)
case class NullRefEntry() extends ExtModelEntry
case class ExtMapEntry(options: Map[String, ExtModelEntry]) extends ExtModelEntry
case class OtherEntry(value: String) extends ExtModelEntry

case class ExtModel(entries: Map[String, ExtModelEntry])
*/
/* basically a 1 to 1 copy of nagini code */
object Converter{
    /*
    def extractHeap(heap: Heap, label: Option[String], target: ExtModel){
        for (chunk <- heap.values) extractChunk(chunk, target, label)
    }
    def extractChunk(chunk:Chunk, target: ExtModel, label: Option[String]) = {
        chunk match{
            case c@BasicChunk(_,_,_,_,_) => {
                c.resourceID match {
                case FieldID => extractField(c, target, label)
                case PredicateID => extractPredicate(c, target, label)
                case _ =>
                }
            }
            case _ => println("WARNING: found non-basic chunk, not implemented")
        }
    }

    def extractField(chunk:BasicChunk, target: ExtModel, label: Option[String]) = {
        val fieldname = chunk.id
        val varname = chunk.args.head 
        val value = evaluateTerm(chunk.snap)
    }
    def extractPredicate(chunk:BasicChunk, target:ExtModel, label:Option[String]) = ???
    */
    def evaluateTerm(term:Term, model: Model) : String = {
        println("evaluating term: " + term.toString)
        term match {
            case Unit => println("of type unit")
                         return "$Snap.unit"
            case IntLiteral(n) =>   println("of type IntLiteral")
                                    return term.toString
            case Null() => 
                            return model.entries("$Ref.null").toString
            case Var(id, sort) => {
                val key = term.toString
                return model.entries(key).toString
            }
            case t@App(app, args) => {
                
                return ""
            }
            case Combine(p0, p1) => {
                return ""
            }
            case First(p) => {
                return ""
            }
            case Second(p) => {
                return ""
            }
            case SortWrapper(t, to) =>  {
                return ""
            }
            case PredicateLookup(pred, psf, args) => {
                return ""
            }
            case _ => return ""
        }
    }
}

class Converter(model: Model, store: Store, heap: Heap, oldHeaps: State.OldHeaps){
//    val extendedModel : ExtModel = ???
    val locals = store.values.keySet



}


/* basically I dont want to lose information since I may not process all
of their types, so this type should still be able to represent the previous
models but give some additional functionality
Should probably be implemented in silver as child class of current model entries */

