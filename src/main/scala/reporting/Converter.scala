package viper.silicon.reporting

import viper.silver.verifier.{
  Model,
  ModelEntry,
  ValueEntry,
  ConstantEntry,
  ApplicationEntry,
  MapEntry
}
import viper.silver.ast
import viper.silicon.interfaces.state.Chunk
import viper.silicon.resources.{FieldID, PredicateID}
import viper.silicon.state.{Store, State, BasicChunk}
import viper.silicon.state.terms.{
  sorts,
  Sort,
  Term,
  Unit,
  IntLiteral,
  BooleanLiteral,
  Null,
  Var,
  App,
  Combine,
  First,
  Second,
  SortWrapper,
  PredicateLookup,
  Rational,
  PermLiteral
}
/* Explanation: (to be removed later)
    To use these new extracted counterexamples, you can use the flag "--counterexample mapped"
    The new trait ExtractedModelEntry should make the counterexamples more readable and extract
    information from the heap, but heap values such as predicates can still be accessed,
    also in a more processed way since all the first/second/Sortwrappers should be gone now and
    replaced with their corresponding values in the extracted Heap fields of the converter class

    A lot of types like sequences etc are not handled yet, and I am not sure if I plan to do so
    since they are not used in Rust

    The various parts in this file should probably be moved out of the interfaces package,
    but for now to keep everything in one place is simpler to work on it.

    To see the advantage of these new counterexamples you can run it on the
    files in src/test/resourcers/demo-counterexamples, the file simple-refs-rec.vpr is
    probably the most interesting.

 */

sealed trait ExtractedModelEntry
case class LitIntEntry(value: BigInt) extends ExtractedModelEntry {
  override def toString = value.toString
}
case class LitBoolEntry(value: Boolean) extends ExtractedModelEntry {
  override def toString = value.toString
}
case class RefEntry(name: String, fields: Map[String, ExtractedModelEntry])
    extends ExtractedModelEntry {
  override def toString: String = {
    val buf = fields
      .map(x => s"\t${x._1} <- ${x._2.toString.split("\n").mkString("\n\t")}\n")
      .mkString("")
    s"Ref ($name) {\n$buf}"
  }
}
case class RecursiveRefEntry(name: String) extends ExtractedModelEntry {
  override def toString = s"recursive reference to $name"
}
case class VarEntry(name: String, sort: Sort) extends ExtractedModelEntry {
  override def toString = name
}
case class NullRefEntry(name: String) extends ExtractedModelEntry {
  override def toString = s"Null($name)"
}
case class OtherEntry(value: String) extends ExtractedModelEntry {
  override def toString = s"$value (unhandled type)"
}

case class unprocessedModelEntry(entry: ValueEntry) extends ExtractedModelEntry

case class ExtractedModel(entries: Map[String, ExtractedModelEntry]) {
  override def toString: String = {
    entries.map(x => s"${x._1} <- ${x._2.toString}").mkString("\n")
  }
}

sealed trait HeapEntry
case class PredHeapEntry(name: String, args: Array[Term]) extends HeapEntry {
  override def toString = s"$name(${args.mkString(", ")})"
}
case class FieldHeapEntry(
    recv: VarEntry,
    field: String,
    perm: Rational,
    sort: Sort
) extends HeapEntry {
  override def toString = s"$recv.$field"
}

case class ExtractedHeap(entries: Map[HeapEntry, String]) {
  override def toString =
    entries.map(x => s"${x._1.toString} <- ${x._2}").mkString("\n")
}

/* basically a 1 to 1 copy of nagini code */
object Converter {
  type ExtractedHeap = Map[HeapEntry, ExtractedModelEntry]

  def snapToOneLine(s: String): String =
    s.filter(_ >= ' ').split(" +").mkString(" ")

  /*def getParts(app: ApplicationWrapper): Array[String] = {
    var res: Array[String] = Array()
    for (part <- ModelParser.getApplication(value)) {
      res = res :+ part
    }
    res
  }*/

  def getFunctionValue(
      model: Model,
      fname: String,
      args: Seq[ValueEntry],
      toSort: Sort
  ): ExtractedModelEntry = {
    val entry: ModelEntry = model.entries(fname)
    val result : ValueEntry = entry match {
      case t: ConstantEntry => t
      case MapEntry(m: Map[Seq[ValueEntry], ValueEntry], els: ValueEntry) =>
        m.get(args).getOrElse(els)
    }
    result match {
      case ConstantEntry(x) => parseConstantEntry(toSort, x)
      case entry: ValueEntry => unprocessedModelEntry(entry)
    }
  }

  def translateSort(s: Sort): String = {
    s match {
      case sorts.Set(els: Sort) => s"Set<${translateSort(els)}>"
      case sorts.Ref            => "$Ref"
      case sorts.Snap           => "$Snap"
      case sorts.Perm           => "$Perm"
      case sorts.Seq(els: Sort) => s"Seq<${translateSort(els)}>"
      case _                    => s.toString
    }
  }

  def parseConstantEntry(s: Sort, t: String): ExtractedModelEntry = {
    s match {
      case sorts.Ref => VarEntry(t, sorts.Ref)
      case sorts.Int => LitIntEntry(BigInt(t))
      case sorts.Bool =>
        t.toLowerCase() match {
          case "true"  => LitBoolEntry(true)
          case "false" => LitBoolEntry(false)
          case x =>
            println(s"error mapping counterexample : $x not a boolean")
            OtherEntry(t)
        }
      case _ =>
        println(s"${t.toString} of sort ${s.toString} not a constant")
        OtherEntry(t)
    }
  }

  def evaluateTerm(term: Term, model: Model): ExtractedModelEntry = {
    term match {
      case Unit              => OtherEntry("$Snap.unit")
      case IntLiteral(x)     => LitIntEntry(x)
      case t: BooleanLiteral => LitBoolEntry(t.value)
      //can null() even occur? because null references on heap are always represented by a variable
      //and from the model we can derive that this variable corresponds to the null reference
      case Null() => VarEntry(model.entries("$Ref.null").toString, sorts.Ref)
      case Var(id@_, sort) =>
        val key = term.toString
        //this can fail : TODO throw and catch exception
        val entry = model.entries(key)
        entry match {
          case t: ApplicationEntry  => unprocessedModelEntry(t)
          case ConstantEntry(value) => parseConstantEntry(sort, value)
        }
      case App(app, args) =>
        /* not tested yet, not sure for which examples this occurs on heap*/
        var fname = app.id + "%limited"
        if (!model.entries.contains(fname)) {
          fname = app.id.toString
          if (!model.entries.contains(fname)) {
            fname = fname.replace("[", "<").replace("]", ">")
          }
        }
        val toSort = app.resultSort
        val argEntries: Seq[ValueEntry] = args
          .map(t => evaluateTerm(t, model))
          .map(_.asInstanceOf[unprocessedModelEntry])
          .map(_.entry)
        getFunctionValue(model, fname, argEntries, toSort)
      case Combine(p0, p1) =>
        /* where does this actually occur? usually snap.combines
      are only found in model not as terms */
        val p0eval = evaluateTerm(p0, model)
        val p1eval = evaluateTerm(p1, model)
        s"($$Snap.combine $p0eval $p1eval)"
        OtherEntry("") //TODO
      case First(p) =>
        val sub = evaluateTerm(p, model)
        sub match {
          case unprocessedModelEntry(ApplicationEntry(name, args)) =>
            assert(name == "$Snap.combine")
            unprocessedModelEntry(args(0))
        }
      case Second(p) =>
        val sub = evaluateTerm(p, model)
        sub match {
          case unprocessedModelEntry(ApplicationEntry(name, args)) =>
            assert(name == "$Snap.combine")
            unprocessedModelEntry(args(1))
        }
      case SortWrapper(t, to) =>
        val sub = evaluateTerm(t, model)
        val arg = sub match {
          case unprocessedModelEntry(p) => p
        }
        val fromSortName: String = translateSort(t.sort)
        val toSortName: String = translateSort(to)
        val fname = s"$$SortWrappers.${fromSortName}To$toSortName"
        getFunctionValue(model, fname, Seq(arg), to)
       

      case PredicateLookup(predname, psf, args) =>
        /* not tested! did never occurr in considered examples */
        /* val lookupFuncName: String = s"$$PSF.lookup_$predname"
        val snap = toSnapTree.apply(args)
        val psfVal = evaluateTerm(psf, model)
        val snapVal = evaluateTerm(snap, model) */
        //getFunctionValue(model, lookupFuncName, arg)
        OtherEntry("PredicateLookup")
      case _ =>
        println("of unhandled type")
        OtherEntry("unhandled Term")
    }
  }

  def extractHeap(h: Iterable[Chunk], model: Model): ExtractedHeap = {
    var target: ExtractedHeap = Map()
    h foreach {
      case c @ BasicChunk(FieldID, _, _, _, _) =>
        val (entry, value) = extractField(c, model)
        target += (entry -> value)
        println(s"${entry.toString} <- ${value.toString}")
      case c @ BasicChunk(PredicateID, _, _, _, _) =>
        val entry = extractPredicate(c)
        println(entry)
        target += (entry -> OtherEntry(""))
      case _ => println("WARNING: not handling non-basic chunks")
    }
    target
  }

  def extractField(
      chunk: BasicChunk,
      model: Model
  ): (HeapEntry, ExtractedModelEntry) = {
    val fieldname = chunk.id.name
    val recvVar = evaluateTerm(chunk.args.head, model).asInstanceOf[VarEntry]
    // this should always be of type VarEntry
    val perm: Rational = chunk.perm match {
      case p: PermLiteral => p.literal
      case _ =>
        println(
          s"Converter: permission field of chunk is not PermLiteral but ${chunk.perm.toString}"
        )
        Rational.zero
    }
    val value = evaluateTerm(chunk.snap, model)

    val entry = FieldHeapEntry(recvVar, fieldname, perm, chunk.snap.sort)
    (entry, value)
  }

  def extractPredicate(chunk: BasicChunk): HeapEntry = {
    //this might be too simple for some cases but for prusti to tell if some
    //variable is part of a class it should be good enough
    //not really sure if the snap value should be added, seems to be same as one of
    //the args in most cases.
    val entry = PredHeapEntry(chunk.id.toString, chunk.args.toArray)
    entry
  }

  def mapLocalVar(
      sort: Sort,
      termEval: ExtractedModelEntry,
      heap: ExtractedHeap,
      model: Model,
      encountered: List[String],
      nullRefName: String
  ): ExtractedModelEntry = {
    sort match {
      case sorts.Int  => termEval
      case sorts.Bool => termEval
      case sorts.Ref =>
        var map: Map[String, ExtractedModelEntry] = Map()
        val name = termEval.toString 
          //if Sort is Ref then termEval has to be of type VarEntry (?)

        //this list helps to recognize and handle cyclic references
        if (name == nullRefName){
          NullRefEntry(name)
        }
        else if (!encountered.contains(name)) {
          val newEncountered = termEval.toString :: encountered
          for ((entry: HeapEntry, value: ExtractedModelEntry) <- heap) {
            entry match {
              case FieldHeapEntry(recv, field, perm @ _, sort) =>
                if (termEval.toString == recv.toString) {
                  //if their names are the same: (dont think this can be true in any other way)
                  val recEntry =
                    mapLocalVar(sort, value, heap, model, newEncountered, nullRefName)
                  map += (field -> recEntry)
                }
              case _ =>
            }
          }
          RefEntry(name, map)
        } else {
          RecursiveRefEntry(termEval.toString)
        }
      case _ => termEval
    }

  }

  def typeToSort(typ: ast.Type): Sort = {
    typ match {
      case ast.Int  => sorts.Int
      case ast.Bool => sorts.Bool
      case ast.Perm => sorts.Perm
      case ast.Ref  => sorts.Ref
      //other types to be implemented
    }
  }

  def mapHeapToStore(
      store: Store,
      heap: ExtractedHeap,
      model: Model
  ): ExtractedModel = {
    var map: Map[String, ExtractedModelEntry] = Map()
    for ((variable: ast.AbstractLocalVar, term: Term) <- store.values) {
      var localtype: Sort = sorts.Unit
      val name = variable match {
        case ast.LocalVar(n, typ) =>
          localtype = typeToSort(typ)
          n
        case ast.Result(typ) =>
          localtype = typeToSort(typ)
          "Result()"
      }
      val nullRefName: String = model.entries("$Ref.null").toString
      val termEval = evaluateTerm(term, model)
      val entry = mapLocalVar(localtype, termEval, heap, model, List(), nullRefName)
      map += (name -> entry)
    }
    val extrModel = ExtractedModel(map)
    extrModel
  }
}

case class Converter(
    model: Model,
    store: Store,
    heap: Iterable[Chunk],
    oldHeaps: State.OldHeaps
) {
  val extractedHeap: Converter.ExtractedHeap =
    Converter.extractHeap(heap, model)
  val extractedHeaps: Map[String, Converter.ExtractedHeap] =
    oldHeaps.map(x => x._1 -> Converter.extractHeap(x._2.values, model))

  val extractedModel = Converter.mapHeapToStore(store, extractedHeap, model)

  val modelAtLabel: Map[String, ExtractedModel] = extractedHeaps.map(x =>
    (x._1 -> Converter.mapHeapToStore(store, x._2, model))
  )
}
