package viper.silicon.interfaces


import viper.silicon.interfaces.state.Chunk
import viper.silicon.resources.{FieldID, PredicateID}
import viper.silicon.state.{Store, State, BasicChunk, Identifier}
import viper.silver.verifier.{Model, ModelEntry, SingleEntry, MapEntry, ModelParser}
import viper.silicon.state.terms.{sorts, Sort, Term, Unit, IntLiteral, Null, Var, App, Combine,
                                  First, Second, SortWrapper, PredicateLookup, toSnapTree}

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
    type SimpleHeap = Map[(Term, String), String]
    
    def snapToOneLine(s:String) : String = s.filter(_ >= ' ').split(" +").mkString(" ")

    def getParts(value: String) : Array[String] = {
        var res : Array[String] = Array()
        for (part <- ModelParser.getApplication(value)) {
            res = res :+ part
        }
        return res
    }

    def getFunctionValue(model: Model, fname: String, args: String) : String = {
        val entry = model.entries(fname)
        entry match {
            case SingleEntry(s) => return s 
            case MapEntry(m: Map[Seq[String], String], els:String) =>
                val filtered = m.filter(x => snapToOneLine(x._1.mkString(" ")) == args)
                if (filtered.size >= 1) {
                    println("found it")
                    return filtered.head._2.toString
                }
                println("didnt find it")
                return els
        }
    }

    def translateSort(s:Sort) : String = {
        s match {
            case sorts.Set(els:Sort) => return "Set<" + translateSort(els)+">"
            case sorts.Ref => return "$Ref"
            case sorts.Snap => return "$Snap"
            case sorts.Perm => return "$Perm"
            case sorts.Seq(els:Sort) => return "Seq<" + translateSort(els)+">"
            case _ => s.toString
        }
    }
    

    def evaluateTerm(term:Term, model: Model) : String = {
        term match {
            case Unit => return "$Snap.unit"
            case IntLiteral(n) => return term.toString
            case Null() => return model.entries("$Ref.null").toString
            case Var(id, sort) => {
                val key = term.toString
                //this can fail : TODO throw and catch exception
                return model.entries(key).toString
            }
            case t@App(app, args) => {
                println("Found type APP")
                var fname = app.id + "%limited"
                if (!model.entries.contains(fname)){
                    fname = app.id.toString
                    if (!model.entries.contains(fname)){
                        fname = fname.replace("[","<").replace("]",">")
                    }
                }
                var arg = snapToOneLine(args.map(x => evaluateTerm(x, model)).mkString(" "))
                return getFunctionValue(model, fname, arg)
            }
            case Combine(p0, p1) => {
                val p0eval = evaluateTerm(p0, model)
                val p1eval = evaluateTerm(p1, model)
                return "($Snap.combine " + p0eval + " " + p1eval + ")"
            }
            case First(p) => {
                val sub = evaluateTerm(p, model)
                if (sub.startsWith("($Snap.combine")){
                    return getParts(sub)(1)
                }
                println("WARNING: one heap entry could not be resolved")
                return ""
            }
            case Second(p) => {
                val sub = evaluateTerm(p, model)
                if (sub.startsWith("($Snap.combine")){
                    return getParts(sub)(2)
                }
                println("WARNING: one heap entry could not be resolved")
                return ""
            }
            case SortWrapper(t, to) =>  {
                val sub = snapToOneLine(evaluateTerm(t, model))
                val fromSortName : String = translateSort(t.sort)
                val toSortName : String = translateSort(to)
                val fname = "$SortWrappers." + fromSortName + "To" + toSortName
                println("looking for " + sub + " in " + fname)
                return getFunctionValue(model, fname, sub)
            }
            case PredicateLookup(predname, psf, args) => {
                val lookupFuncName : String = "$PSF.lookup_" + predname
                val snap = toSnapTree.apply(args)
                val psfVal = evaluateTerm(psf, model)
                val snapVal = evaluateTerm(snap, model)
                val arg = snapToOneLine(psfVal + " " + snapVal)
                return getFunctionValue(model, lookupFuncName, arg)
            }
            case _ =>   println("of unhandled type") 
                        return ""
        }
    }

    def extractHeap(h:Iterable[Chunk], model: Model) : SimpleHeap = {
        var target : SimpleHeap = Map()
        for (chunk <- h) {
            chunk match {
                case c@BasicChunk(resId, id, args, snap, perm) => {
                    resId match {
                        case FieldID => val (recv, field, value) = extractField(c, model)
                                        target += ((recv, field) -> value)                                        
                        case PredicateID => println(".------------------------------------------------------------------------------------------------------------------------------")
                        case _ => 
                    }
                    
                }
                case _ => println("WARNING: not handling non-basic chunks")
            }
        }
        return target
    }

    def extractField(chunk:BasicChunk, model: Model) : (Term, String, String) =  {
        val fieldname = chunk.id.name //String
        var recv : Term = chunk.args.head //Term
        var recvString = recv.toString
        recv match {
            case Var(id, sort) => //no evaluation necessary
            case t: Term => recvString = evaluateTerm(recv, model)
                            recv = Var(Identifier.apply(recvString), sorts.Ref)
        }
        println("trying to get value of " + recvString + "." + fieldname)
        val value = evaluateTerm(chunk.snap, model) //String
        println("value is : " + value)
        return (recv, fieldname, value)
    }

    def extractPredicate(chunk: BasicChunk, model: Model) {
        val predName = chunk.id.name
        val args = chunk.args
    }
    
    def simpleHeapAsModel(simpleHeap: SimpleHeap, label: String = "") : Model = {
        var entries : Map[String, ModelEntry] = Map()
        for (((term, field), value) <- simpleHeap) {
            entries += (("extr. heap: " + label + " : " + term.toString + " " + field) -> SingleEntry(value))
        }
        return Model(entries)
    }
    
}

case class Converter(model: Model, store: Store, heap: Iterable[Chunk], oldHeaps: State.OldHeaps){
//    val extendedModel : ExtModel = ???
    val extractedHeap : Converter.SimpleHeap = Converter.extractHeap(heap, model)
    val extractedHeaps : Map[String, Converter.SimpleHeap] = oldHeaps.map(x => x._1 -> Converter.extractHeap(x._2.values, model))
    val heapModel : Model = Converter.simpleHeapAsModel(extractedHeap)
}


/* basically I dont want to lose information since I may not process all
of their types, so this type should still be able to represent the previous
models but give some additional functionality
Should probably be implemented in silver as child class of current model entries */

