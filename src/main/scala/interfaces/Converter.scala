package viper.silicon.interfaces

import viper.silver.verifier.{Model, ModelEntry, SingleEntry, MapEntry, ModelParser}
import viper.silver.ast

import viper.silicon.interfaces.state.Chunk
import viper.silicon.resources.{FieldID, PredicateID}
import viper.silicon.state.{Store, State, BasicChunk, Identifier}
import viper.silicon.state.terms.{sorts, Sort, Term, Unit, IntLiteral, BooleanLiteral, Null, Var, App, Combine,
                                  First, Second, SortWrapper, PredicateLookup, toSnapTree, Rational, PermLiteral}


/* Some new classes to describe a more informative model */

sealed trait ExtractedModelEntry
case class LitIntEntry(value: BigInt) extends ExtractedModelEntry {
    override def toString = value.toString
}
case class LitBoolEntry(value: Boolean) extends ExtractedModelEntry {
    override def toString = value.toString
}
case class RefEntry(fields: Map[String, ExtractedModelEntry]) extends ExtractedModelEntry {
    override def toString : String = {
        var buf = "Ref : { \n"
        for ((name, entry) <- fields) {
            buf += "\t" + name + " <- " + entry.toString.split("\n").mkString("\n\t") + "\n"
        }
        buf += "}"
        return buf
    }
}
case class VarEntry(name: String) {
    override def toString = name
}
case class NullRefEntry() extends ExtractedModelEntry {
    override def toString = "Null()"
}
case class OtherEntry(value: String) extends ExtractedModelEntry {
    override def toString = value + "(unhandled type)"
}

case class ExtractedModel(entries: Map[String, ExtractedModelEntry]) {
    override def toString : String = {
        var buf = ""
        for ((name, entry) <- entries) {
            buf += name + " <- " + entry.toString + "\n"
        }
        return buf
    }
}

sealed trait HeapEntry
case class PredHeapEntry(name: String, args: Array[Term]) extends HeapEntry {
    override def toString = name + "(" + args.mkString(", ") +")"
}
case class FieldHeapEntry(recv: String, field: String, perm: Rational, typ: Option[ast.Type]) extends HeapEntry {
    override def toString = recv + "." + field
}

case class ExtractedHeap(entries: Map[HeapEntry, String]) {
    override def toString = entries.map(x => x._1.toString + " <- " + x._2).mkString("\n")
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

    def sortToType(s:Sort) : Option[ast.Type] = {
        s match {
            case sorts.Ref => return Some(ast.Ref)
            case sorts.Int => return Some(ast.Int)
            case sorts.Bool => return Some(ast.Bool)
            case sorts.Perm => return Some(ast.Perm)
            case _ => println("This type of Heap Field can not be handled : " + s.toString)
                      return None
        }
    }
    

    def evaluateTerm(term:Term, model: Model) : String = {
        term match {
            case Unit => return "$Snap.unit"
            case IntLiteral(n) => return term.toString
            case t:BooleanLiteral => return t.value.toString
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
        var recvString = evaluateTerm(chunk.args.head, model) //Term
        
        val perm : Rational = chunk.perm match {
            case p : PermLiteral => p.literal
            case _ => println("Converter: permission field of chunk is not PermLiteral but " + chunk.perm.toString)
                      Rational.zero
        }
        val value = evaluateTerm(chunk.snap, model) //String
        val typ : Option[ast.Type] = sortToType(chunk.snap.sort)
        val entry = FieldHeapEntry(recvString, fieldname, perm, typ)
        return (entry, value)
    }

    def extractPredicate(chunk: BasicChunk, model: Model) : HeapEntry = {
        //this might be too simple for some cases but for prusti to tell if some 
        //variable is part of a class it should be good enough
        //not really sure if the snap value should be added, seems to be same as one of 
        //the args in most cases.
        val entry = PredHeapEntry(chunk.id.toString, chunk.args.toArray) 
        return entry
    } 

    def mapLocalVar(expectedType: ast.Type, termEval: String, heap: ExtractedHeap, model: Model) : ExtractedModelEntry = {
        expectedType match {
            case ast.Int => //value is possibly stored directly in store, but if it's stored in the model
                            //we will have to parse it so we evaluate it anyways and parse it..
                val value = BigInt(termEval) //TODO: catch exception if parsing fails. not sure if this could occur
                return LitIntEntry(value)

            case ast.Bool => 
                val b : Boolean = termEval.toLowerCase() match {
                    case "true" => true
                    case "false" => false
                    case x:String => println("error mapping counterexample : " + x + " not a boolean")
                              return OtherEntry(termEval)
                }
                return LitBoolEntry(b)
            case ast.Ref =>
                println("trying to map Ref: " + termEval)
                var map : Map[String, ExtractedModelEntry] = Map()
                for ((entry: HeapEntry, value: String) <- heap) {
                    entry match {
                        case FieldHeapEntry(recv, field, perm, typ) =>
                            if (recv == termEval) {
                                if (typ.isDefined) {
                                    val recEntry = mapLocalVar(typ.get, value, heap, model)
                                    map += (field -> recEntry)
                                } else {
                                    map += (field -> OtherEntry(value))
                                }
                            }
                        case _ => 
                    }
                }
                return RefEntry(map)
            case _ => return OtherEntry(termEval)
        }
        
    }


    def mapHeapToStore(store: Store, heap: ExtractedHeap, model: Model) : ExtractedModel = {
        var map : Map[String, ExtractedModelEntry] = Map()
        for ((variable: ast.AbstractLocalVar, term: Term) <- store.values) {
            var localtype : ast.Type = ast.Int
            val name = variable match {
                case ast.LocalVar(n, typ) => 
                    localtype = typ
                    n
                case ast.Result(typ) => 
                    localtype = typ
                    "Result()"
            }
            val termEval = evaluateTerm(term, model)
            val entry = mapLocalVar(localtype, termEval, heap, model)
            map += (name -> entry)
        }
        val extrModel = ExtractedModel(map)
        println(extrModel.toString)
        return extrModel
    }

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

    def extractedModeltoModel(extModel: ExtractedModel) : Model = {
        val map = extModel.entries.map(x => (x._1 -> SingleEntry(x._2.toString)))
        return Model(map)
    }
}   
    

case class Converter(model: Model, store: Store, heap: Iterable[Chunk], oldHeaps: State.OldHeaps){
//    val extendedModel : ExtModel = ???
    val extractedHeap : Converter.ExtractedHeap = Converter.extractHeap(heap, model)
    val extractedHeaps : Map[String, Converter.ExtractedHeap] = oldHeaps.map(x => x._1 -> Converter.extractHeap(x._2.values, model))
    val heapModel : Map[String, ModelEntry] = {
        Converter.outputOldHeaps(extractedHeaps)
        Converter.mapHeapToStore(store, extractedHeap, model)
        Converter.heapToModel(extractedHeap, "")
    }
    val extModel = Converter.extractedModeltoModel(Converter.mapHeapToStore(store, extractedHeap, model))
    
}


