package viper.silicon.interfaces

import viper.silver.verifier.{
  Model,
  ModelEntry,
  SingleEntry,
  MapEntry,
  ModelParser
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
  toSnapTree,
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
case class RefEntry(fields: Map[String, ExtractedModelEntry])
    extends ExtractedModelEntry {
  override def toString: String = {
    val buf = fields
      .map(x => s"\t${x._1} <- ${x._2.toString.split("\n").mkString("\n\t")}\n")
      .mkString("")
    s"Ref {\n$buf}"
  }
}
case class VarEntry(name: String) {
  override def toString = name
}
case class NullRefEntry() extends ExtractedModelEntry {
  override def toString = "Null()"
}
case class OtherEntry(value: String) extends ExtractedModelEntry {
  override def toString = s"$value (unhandled type)"
}

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
    recv: String,
    field: String,
    perm: Rational,
    typ: Option[ast.Type]
) extends HeapEntry {
  override def toString = s"$recv.$field"
}

case class ExtractedHeap(entries: Map[HeapEntry, String]) {
  override def toString =
    entries.map(x => s"${x._1.toString} <- ${x._2}").mkString("\n")
}

/* basically a 1 to 1 copy of nagini code */
object Converter {
  type ExtractedHeap = Map[HeapEntry, String]

  def snapToOneLine(s: String): String =
    s.filter(_ >= ' ').split(" +").mkString(" ")

  def getParts(value: String): Array[String] = {
    var res: Array[String] = Array()
    for (part <- ModelParser.getApplication(value)) {
      res = res :+ part
    }
    res
  }

  def getFunctionValue(model: Model, fname: String, args: String): String = {
    val entry: ModelEntry = model.entries(fname)
    entry match {
      case SingleEntry(s) => s
      case MapEntry(m: Map[Seq[String], String], els: String) =>
        val filtered = m.filter(x => snapToOneLine(x._1.mkString(" ")) == args)
        if (filtered.nonEmpty) {
          filtered.head._2.toString
        } else {
          els
        }
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

  def sortToType(s: Sort): Option[ast.Type] = {
    s match {
      case sorts.Ref  => Some(ast.Ref)
      case sorts.Int  => Some(ast.Int)
      case sorts.Bool => Some(ast.Bool)
      case sorts.Perm => Some(ast.Perm)
      case _ =>
        println(s"This type of Heap Field can not be handled : ${s.toString}")
        None
    }
  }

  def evaluateTerm(term: Term, model: Model): String = {
    term match {
      case Unit              => "$Snap.unit"
      case IntLiteral(n)     => term.toString
      case t: BooleanLiteral => t.value.toString
      case Null()            => model.entries("$Ref.null").toString
      case Var(id, sort) =>
        val key = term.toString
        //this can fail : TODO throw and catch exception
        model.entries(key).toString
      case t @ App(app, args) =>
        /* not tested yet, not sure for which examples this occurs on heap*/
        var fname = app.id + "%limited"
        if (!model.entries.contains(fname)) {
          fname = app.id.toString
          if (!model.entries.contains(fname)) {
            fname = fname.replace("[", "<").replace("]", ">")
          }
        }
        var arg = snapToOneLine(
          args.map(x => evaluateTerm(x, model)).mkString(" ")
        )
        getFunctionValue(model, fname, arg)
      case Combine(p0, p1) =>
        val p0eval = evaluateTerm(p0, model)
        val p1eval = evaluateTerm(p1, model)
        s"($$Snap.combine $p0eval $p1eval)"
      case First(p) =>
        val sub = evaluateTerm(p, model)
        if (sub.startsWith("($Snap.combine")) {
          getParts(sub)(1)
        } else {
          println("WARNING: one heap entry could not be resolved")
          ""
        }
      case Second(p) =>
        val sub = evaluateTerm(p, model)
        if (sub.startsWith("($Snap.combine")) {
          getParts(sub)(2)
        } else {
          println("WARNING: one heap entry could not be resolved")
          ""
        }
      case SortWrapper(t, to) =>
        val sub = snapToOneLine(evaluateTerm(t, model))
        val fromSortName: String = translateSort(t.sort)
        val toSortName: String = translateSort(to)
        val fname = s"$$SortWrappers.${fromSortName}To$toSortName"
        getFunctionValue(model, fname, sub)
      case PredicateLookup(predname, psf, args) =>
        /* not tested! did never occurr in considered examples */
        val lookupFuncName: String = s"$$PSF.lookup_$predname"
        val snap = toSnapTree.apply(args)
        val psfVal = evaluateTerm(psf, model)
        val snapVal = evaluateTerm(snap, model)
        val arg = snapToOneLine(s"$psfVal $snapVal")
        getFunctionValue(model, lookupFuncName, arg)
      case _ =>
        println("of unhandled type")
        ""
    }
  }

  def extractHeap(h: Iterable[Chunk], model: Model): ExtractedHeap = {
    var target: ExtractedHeap = Map()
    h foreach {
      case c @ BasicChunk(FieldID, id, args, snap, perm) =>
        val (entry, value) = extractField(c, model)
        target += (entry -> value)
      case c @ BasicChunk(PredicateID, id, args, snap, perm) =>
        val entry = extractPredicate(c, model)
        target += (entry -> "")
      case c @ BasicChunk(resId, id, args, snap, perm) =>
        println("chunks for magic wands not implemented")
      case _ => println("WARNING: not handling non-basic chunks")
    }
    target
  }

  def extractField(chunk: BasicChunk, model: Model): (HeapEntry, String) = {
    val fieldname = chunk.id.name
    var recvString = evaluateTerm(chunk.args.head, model)

    val perm: Rational = chunk.perm match {
      case p: PermLiteral => p.literal
      case _ =>
        println(
          s"Converter: permission field of chunk is not PermLiteral but ${chunk.perm.toString}"
        )
        Rational.zero
    }
    val value = evaluateTerm(chunk.snap, model) //String
    val typ: Option[ast.Type] = sortToType(chunk.snap.sort)
    val entry = FieldHeapEntry(recvString, fieldname, perm, typ)
    (entry, value)
  }

  def extractPredicate(chunk: BasicChunk, model: Model): HeapEntry = {
    //this might be too simple for some cases but for prusti to tell if some
    //variable is part of a class it should be good enough
    //not really sure if the snap value should be added, seems to be same as one of
    //the args in most cases.
    val entry = PredHeapEntry(chunk.id.toString, chunk.args.toArray)
    entry
  }

  def mapLocalVar(
      expectedType: ast.Type,
      termEval: String,
      heap: ExtractedHeap,
      model: Model
  ): ExtractedModelEntry = {
    expectedType match {
      case ast.Int => //value is possibly stored directly in store, but if it's stored in the model
        //we will have to parse it so we evaluate it anyways and parse it..
        val value = BigInt(termEval)
        //TODO: catch exception if parsing fails. not sure if this could occur
        LitIntEntry(value)

      case ast.Bool =>
        termEval.toLowerCase() match {
          case "true"  => LitBoolEntry(true)
          case "false" => LitBoolEntry(false)
          case x: String =>
            println(s"error mapping counterexample : $x not a boolean")
            OtherEntry(termEval)
        }
      case ast.Ref =>
        var map: Map[String, ExtractedModelEntry] = Map()
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
        RefEntry(map)
      case _ => OtherEntry(termEval)
    }

  }

  def mapHeapToStore(
      store: Store,
      heap: ExtractedHeap,
      model: Model
  ): ExtractedModel = {
    var map: Map[String, ExtractedModelEntry] = Map()
    for ((variable: ast.AbstractLocalVar, term: Term) <- store.values) {
      var localtype: ast.Type = ast.Int
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
    extrModel
  }
}

case class Converter(
    model: Model,
    store: Store,
    heap: Iterable[Chunk],
    oldHeaps: State.OldHeaps
) {
//    val extendedModel : ExtModel = ???
  val extractedHeap: Converter.ExtractedHeap =
    Converter.extractHeap(heap, model)
  val extractedHeaps: Map[String, Converter.ExtractedHeap] =
    oldHeaps.map(x => x._1 -> Converter.extractHeap(x._2.values, model))
  val extractedModel = Converter.mapHeapToStore(store, extractedHeap, model)
  val modelAtLabel: Map[String, ExtractedModel] = extractedHeaps.map(x =>
    (x._1 -> Converter.mapHeapToStore(store, x._2, model))
  )
}
