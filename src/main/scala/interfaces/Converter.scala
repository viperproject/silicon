package viper.silicon.interfaces

import viper.silver.verifier.{Model, ModelEntry, SingleEntry, MapEntry, ModelParser}
import viper.silver.ast

import viper.silicon.interfaces.state.Chunk
import viper.silicon.resources.{FieldID, PredicateID}
import viper.silicon.state.{Store, State, BasicChunk, Identifier}
import viper.silicon.state.terms.{sorts, Sort, Term, Unit, IntLiteral, Null, Var, App, Combine,
                                  First, Second, SortWrapper, PredicateLookup, toSnapTree, Rational, PermLiteral}


/* Some new classes to describe a more informative model */

sealed trait ExtModelEntry
case class LitIntEntry(value: BigInt) extends ExtModelEntry 
case class LitBoolEntry(value: Boolean) extends ExtModelEntry
case class RefEntry(fields: Map[String, ExtModelEntry]) extends ExtModelEntry
case class VarEntry(name: String)
case class NullRefEntry() extends ExtModelEntry
case class ExtMapEntry(options: Map[String, ExtModelEntry]) extends ExtModelEntry
case class OtherEntry(value: String) extends ExtModelEntry

case class ExtModel(entries: Map[String, ExtModelEntry])

sealed trait HeapEntry
case class PredHeapEntry(name: String, args: Array[Term]) extends HeapEntry {
    override def toString = name + "(" + args.mkString(", ") +")"
}
case class FieldHeapEntry(recv: Term, field: String, perm: Rational) extends HeapEntry {
    override def toString = recv.toString + "." + field
}



/* basically a 1 to 1 copy of nagini code */
object Converter{    
    type ExtractedHeap = Map[HeapEntry, String]
    def snapToOneLine(s:String) : String = s.filter(_ >= ' ').split(" +").mkString(" ")

    def getParts(value: String) : Array[String] = {
        var res : Array[String] = Array()
        for (part <- ModelParser.getApplication(value)) {
            res = res :+ part
        }
        return res
    }

    def getFunctionValue(model: Model, fname: String, args: String) : String = {
        val entry : ModelEntry = model.entries(fname)
        entry match {
            case SingleEntry(s) => return s 
            case MapEntry(m: Map[Seq[String], String], els:String) =>
                val filtered = m.filter(x => snapToOneLine(x._1.mkString(" ")) == args)
                if (filtered.size >= 1) {
                    return filtered.head._2.toString
                }
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
                /* not tested yet, not sure for which examples this occurs on heap*/
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
                return getFunctionValue(model, fname, sub)
            }
            case PredicateLookup(predname, psf, args) => {
                /* not tested! did never occurr in considered examples */
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

    def extractHeap(h:Iterable[Chunk], model: Model) : ExtractedHeap = {
        var target : ExtractedHeap = Map()
        for (chunk <- h) {
            chunk match {
                case c@BasicChunk(resId, id, args, snap, perm) => {
                    resId match {
                        case FieldID => val (entry, value) = extractField(c, model)
                                        target += (entry -> value)                                        
                        case PredicateID => val entry = extractPredicate(c, model)
                                            target += (entry -> "")

                        case _ => println("chunks for magic wands not implemented")
                    }
                    
                }
                case _ => println("WARNING: not handling non-basic chunks")
            }
        }
        return target
    }

    def extractField(chunk:BasicChunk, model: Model) : (HeapEntry, String) =  {
        val fieldname = chunk.id.name //String
        var recv : Term = chunk.args.head //Term
        recv match {
            case Var(id, sort) => //no evaluation necessary
            case t: Term => val recvString = evaluateTerm(recv, model)
                            recv = Var(Identifier.apply(recvString), sorts.Ref)
                            //has to be of sort Ref if there are fields to it
        }
        val perm : Rational = chunk.perm match {
            case p : PermLiteral => p.literal
            case _ => println("Converter: permission field of chunk is not PermLiteral but " + chunk.perm.toString)
                      Rational.zero
        }
        val value = evaluateTerm(chunk.snap, model) //String
        val entry = FieldHeapEntry(recv, fieldname, perm)
        return (entry, value)
    }

    def extractPredicate(chunk: BasicChunk, model: Model) : HeapEntry = {
        //this might be too simple for some cases but for prusti to tell if some 
        //variable is part of a class it should be good enough
        //not really sure if the snap value is needed
        val entry = PredHeapEntry(chunk.id.toString, chunk.args.toArray) 
        return entry
    }    
    /*
    def extractRecursive(term: Term) : ExtModelEntry {
        term match {
            case Var(id, sort) => 
            case  => 
        }
    }
    
    def extModelFromHeap(heap: SimpleHeap, store:Store, model: Model) {
        for ((variable: ast.AbstractLocalVar, term: Term) <- store.values) {
            val name = variable match {
                ast.LocalVar(n, typ) => n
                ast.Result(typ) => "Result()"
            }
            val sort = term match {
                case Var(name, sort) => sort
                case _ => println("Converter.extModelFromHeap(), usually the store only contains 
                    only variables, no concrete values, this case has yet to be handled")
            }

        }
    */

    // might not be possible to display these new models with the old Model structure,
    // since those are unordered and we would want entries grouped.
    // so for now they are just printed so they stay in their blocks
    def heapToModel(heap: ExtractedHeap, label: String) : Map[String, ModelEntry] = {
        println("Processed Heap at label: " + label )
        for (x <- heap) {
            x._1 match {
                case h:FieldHeapEntry => println("\t" + h.toString + " <- " + x._2)
                case h:PredHeapEntry => println("\t" + h.toString)
            }
        }
        Map()
    }

    def outputOldHeaps(heaps: Map[String, Converter.ExtractedHeap]) {
        for ((lbl, heap) <- heaps) {
            heapToModel(heap, lbl)
        }
    }
}   
    

case class Converter(model: Model, store: Store, heap: Iterable[Chunk], oldHeaps: State.OldHeaps){
//    val extendedModel : ExtModel = ???
    val extractedHeap : Converter.ExtractedHeap = Converter.extractHeap(heap, model)
    val extractedHeaps : Map[String, Converter.ExtractedHeap] = oldHeaps.map(x => x._1 -> Converter.extractHeap(x._2.values, model))
    val heapModel : Map[String, ModelEntry] = {
        Converter.outputOldHeaps(extractedHeaps)
        Converter.heapToModel(extractedHeap, "")
    }
}


