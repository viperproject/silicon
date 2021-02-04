package viper.silicon.reporting

import scala.util.{Try, Success}
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

//Classes for final extracted Model Entries
case class ExtractedModel(entries: Map[String, ExtractedModelEntry]) {
  override def toString: String = {
    entries.map(x => s"${x._1} <- ${x._2.toString}").mkString("\n")
  }
}

sealed trait ExtractedModelEntry
case class LitIntEntry(value: BigInt) extends ExtractedModelEntry {
  override def toString = value.toString
  def negate: LitIntEntry = LitIntEntry(-value)
}
case class LitBoolEntry(value: Boolean) extends ExtractedModelEntry {
  override def toString = value.toString
}
case class RefEntry(
    name: String,
    fields: Map[String, (ExtractedModelEntry, Option[Rational])]
) extends ExtractedModelEntry {
  override def toString: String = {
    val buf = fields
      .map(x =>
        s"\t${x._1}(perm: ${x._2._2.map(_.toString).getOrElse("?")}) <- ${x._2._1.toString.split("\n").mkString("\n\t")}\n"
      )
      .mkString("")
    s"Ref ($name) {\n$buf}"
  }
}
case class NullRefEntry(name: String) extends ExtractedModelEntry {
  override def toString = s"Null($name)"
}
case class RecursiveRefEntry(name: String) extends ExtractedModelEntry {
  override def toString = s"recursive reference to $name"
}
case class VarEntry(name: String, sort: Sort) extends ExtractedModelEntry {
  override def toString = name
}

case class OtherEntry(value: String) extends ExtractedModelEntry {
  override def toString = s"$value"
}
case class SeqEntry(name: String, values: List[ExtractedModelEntry])
    extends ExtractedModelEntry {
  //counterexample sequences are often very long. Does it make sense to print
  //all of their entries?
  override def toString = s"($name): [${values.map(_.toString).mkString(", ")}]"
}

case class UnprocessedModelEntry(entry: ValueEntry) extends ExtractedModelEntry

// processed Heap representation:
sealed trait HeapEntry

case class ExtractedHeap(entries: List[HeapEntry])

case class PredHeapEntry(name: String, args: Array[Term]) extends HeapEntry {
  override def toString = s"$name(${args.mkString(", ")})"
}
case class FieldHeapEntry(
    recv: VarEntry,
    field: String,
    perm: Option[Rational],
    sort: Sort,
    entry: ExtractedModelEntry
) extends HeapEntry {
  override def toString = s"$recv.$field"
}

case class UnresolvedHeapEntry(chunk: Chunk, reason: String) extends HeapEntry {
  override def toString = s"$chunk (not further processed because: $reason)"
}

object Converter {
  def getFunctionValue(
      model: Model,
      fname: String,
      args: Seq[ValueEntry],
      toSort: Sort
  ): ExtractedModelEntry = {
    val entry: Option[ModelEntry] = model.entries.get(fname)
    entry match {
      case Some(MapEntry(m, els)) =>
        getConstantEntry(toSort, m.get(args).getOrElse(els))
      case Some(m) => getConstantEntry(toSort, m)
      case None    => OtherEntry("${fname}-application but not found in model")
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

  def getConstantEntry(s: Sort, m: ModelEntry): ExtractedModelEntry = {
    s match {
      case sorts.Ref => VarEntry(m.toString, sorts.Ref)
      case sorts.Int =>
        m match {
          case ConstantEntry(x) => LitIntEntry(BigInt(x))
          case ApplicationEntry(name, args) =>
            //this is needed because negative integers are stored as ApplicationEntries
            val res = getConstantEntry(s, args(0))
            res match {
              case l @ LitIntEntry(_) =>
                if (name == "-") {
                  l.negate
                } else {
                  //are there other special cases for integers?
                  OtherEntry(s"$m: non constant ApplicationEntry (unexpected)")
                }
              case _ => OtherEntry(s"$m instead of integer literal (unexpected)")
            }
          case _ => OtherEntry(s"$m instead of integer literal (unexpected)")
        }
      case sorts.Bool =>
        m.toString.toLowerCase() match {
          case "true"  => LitBoolEntry(true)
          case "false" => LitBoolEntry(false)
          case x =>
            OtherEntry(s"$x instead of boolean literal (unexpected)")
        }
      case sorts.Seq(_) => VarEntry(m.toString, s) // will be resolved later
      case _ =>
        m match {
          case e: ValueEntry => UnprocessedModelEntry(e)
          case e: MapEntry =>
            OtherEntry(s"$e ApplicationEntry as Constant (unexpected)")
        }
    }
  }

  def evaluateTerm(term: Term, model: Model): ExtractedModelEntry = {
    term match {
      case Unit              => OtherEntry("$Snap.unit")
      case IntLiteral(x)     => LitIntEntry(x)
      case t: BooleanLiteral => LitBoolEntry(t.value)
      case Null()            => VarEntry(model.entries("$Ref.null").toString, sorts.Ref)
      case Var(_, sort) =>
        val key: String = term.toString
        val entry: Option[ModelEntry] = model.entries.get(key)
        entry
          .map(x => getConstantEntry(sort, x))
          .getOrElse(
            OtherEntry(s"$term variable not found in model (unexpected)")
          )

      case App(app, args) =>
        /* not tested yet, not sure for which examples this occurs on heap*/
        var fname = s"${app.id}%limited"
        if (!model.entries.contains(fname)) {
          fname = app.id.toString
          if (!model.entries.contains(fname)) {
            fname = fname.replace("[", "<").replace("]", ">")
          }
        }
        val toSort = app.resultSort
        val argEntries: Seq[ValueEntry] = args
          .map(t => evaluateTerm(t, model))
          .map(_.asInstanceOf[UnprocessedModelEntry])
          .map(_.entry)
        getFunctionValue(model, fname, argEntries, toSort)
      case Combine(_, _) =>
        /*
        This is a left-over from nagini, not sure if this needs to be
        reimplemented
        val p0eval = evaluateTerm(p0, model)
        val p1eval = evaluateTerm(p1, model)
         */
        println("DEBUG: Combine-Term encountered")
        OtherEntry("Combine-Term (unhandled)") //TODO
      case First(p) =>
        val sub = evaluateTerm(p, model)
        sub match {
          case UnprocessedModelEntry(ApplicationEntry(name, args)) =>
            if (name == "$Snap.combine") {
              UnprocessedModelEntry(args(0))
            } else {
              OtherEntry(s"First($p) unapplicable (unexpected)")
            }
          case _ => OtherEntry(s"First($p) unapplicable (unexpected)")
        }
      case Second(p) =>
        val sub = evaluateTerm(p, model)
        sub match {
          case UnprocessedModelEntry(ApplicationEntry(name, args)) =>
            if (name == "$Snap.combine") {
              UnprocessedModelEntry(args(1))
            } else {
              OtherEntry(s"Second($p) unapplicable (unexpected)")
            }
          case _ => OtherEntry(s"Second($p) unapplicable (unexpected)")
        }
      case SortWrapper(t, to) =>
        val sub = evaluateTerm(t, model)
        val arg = sub match {
          case UnprocessedModelEntry(p) => Some(p)
          case _                        => None
        }
        val fromSortName: String = translateSort(t.sort)
        val toSortName: String = translateSort(to)
        val fname = s"$$SortWrappers.${fromSortName}To$toSortName"
        if (arg == None) {
          OtherEntry("Sortwrapper(sub) unapplicable (unexpected)")
        } else {
          getFunctionValue(model, fname, Seq(arg.get), to)
        }

      case PredicateLookup(predname, _, _) =>
        /* not tested! did never occurr in considered examples */
        /* val lookupFuncName: String = s"$$PSF.lookup_$predname"
        val snap = toSnapTree.apply(args)
        val psfVal = evaluateTerm(psf, model)
        val snapVal = evaluateTerm(snap, model) */
        //getFunctionValue(model, lookupFuncName, arg)
        OtherEntry(s"PredicateLookup $predname (unhandled)")
      case _ =>
        OtherEntry(s"$term (unhandled)")
    }
  }

  def extractHeap(h: Iterable[Chunk], model: Model): ExtractedHeap = {
    var entries: List[HeapEntry] = List()
    h foreach {
      case c @ BasicChunk(FieldID, _, _, _, _) =>
        val entry = extractField(c, model)
        entries = entries :+ entry
        println(s"DEBUG: $entry")
      case c @ BasicChunk(PredicateID, _, _, _, _) =>
        val entry = extractPredicate(c)
        println(s"DEBUG (heap): $entry")
        entries = entries :+ entry
      case c: BasicChunk =>
        entries = entries :+ UnresolvedHeapEntry(c, "Magic Wands not supported")
      case c =>
        entries =
          entries :+ UnresolvedHeapEntry(c, "Non-basic chunks not supported")
    }
    ExtractedHeap(entries)
  }

  def extractField(chunk: BasicChunk, model: Model): HeapEntry = {
    val fieldname = chunk.id.name
    val recv = evaluateTerm(chunk.args.head, model)
    val recvVar: Try[VarEntry] = Try(recv.asInstanceOf[VarEntry])
    // this should always be of type VarEntry

    val perm: Option[Rational] = chunk.perm match {
      case p: PermLiteral => Some(p.literal)
      case _              => None
    }
    val value = evaluateTerm(chunk.snap, model)
    recvVar match {
      case Success(varEntry) =>
        FieldHeapEntry(varEntry, fieldname, perm, chunk.snap.sort, value)
      case _ =>
        UnresolvedHeapEntry(
          chunk,
          "the receiver term is not a variable (unexpected)"
        )
    }
  }

  def extractPredicate(chunk: BasicChunk): HeapEntry = {
    //this might be too simple for some cases but for prusti to tell if some
    //variable is part of a class it should be good enough
    //not really sure if the snap value should be added, seems to be same as one of
    //the args in most cases.
    val entry = PredHeapEntry(chunk.id.toString, chunk.args.toArray)
    entry
  }

  def extractSequence(
      model: Model,
      heap: ExtractedHeap,
      nullRefName: String,
      name: String,
      elementSort: Sort,
      encountered: List[String]
  ): ExtractedModelEntry = {
    if (!encountered.contains(name)) {
      val newEncountered = name :: encountered
      //hopefully Seq_len can only contain integers
      val lenTry: Try[Int] = Try(
        getFunctionValue(
          model,
          "Seq_length",
          Seq(ConstantEntry(name)),
          sorts.Int
        ).asInstanceOf[LitIntEntry].value.toInt
      )
      lenTry match {
        case Success(x) =>
          val len: Int = x
          var values: List[ExtractedModelEntry] = List()
          for (i <- 0 to len) {
            val valueEntry: ExtractedModelEntry = getFunctionValue(
              model,
              "Seq_index",
              Seq(ConstantEntry(name), ConstantEntry(i.toString)),
              elementSort
            )
            //valueEntry might be a Ref or Sequence and has to be mapped as well
            val finalEntry: ExtractedModelEntry = mapLocalVar(
              elementSort,
              valueEntry,
              heap,
              model,
              newEncountered,
              nullRefName
            )
            values = values :+ finalEntry
          }
          SeqEntry(name, values)
        case _ => OtherEntry("unresolvable-length Sequence (unexpected)")
      }
    } else {
      RecursiveRefEntry(name)
    }
  }

  def mapLocalVar(
      sort: Sort,
      termEval: ExtractedModelEntry,
      heap: ExtractedHeap,
      model: Model,
      encountered: List[String],
      nullRefName: String
  ): ExtractedModelEntry = {
    val name = termEval.toString
    sort match {
      case sorts.Int  => termEval
      case sorts.Bool => termEval
      case sorts.Ref =>
        var map: Map[String, (ExtractedModelEntry, Option[Rational])] = Map()
        //if Sort is Ref then termEval has to be of type VarEntry (?)

        //this list helps to recognize and handle cyclic references
        if (name == nullRefName) {
          NullRefEntry(name)
        } else if (!encountered.contains(name)) {
          val newEncountered = name :: encountered
          for (entry: HeapEntry <- heap.entries) {
            entry match {
              case FieldHeapEntry(recv, field, perm @ _, sort, value) =>
                if (termEval == recv) {
                  val recEntry =
                    mapLocalVar(
                      sort,
                      value,
                      heap,
                      model,
                      newEncountered,
                      nullRefName
                    )
                  map += (field -> (recEntry, perm))
                }
              case _ =>
            }
          }
          RefEntry(name, map)
        } else {
          RecursiveRefEntry(name)
        }
      case sorts.Seq(elementSort) =>
        extractSequence(
          model,
          heap,
          nullRefName,
          name,
          elementSort,
          encountered
        )
      case _ => termEval
    }

  }

  def typeToSort(typ: ast.Type): Sort = {
    typ match {
      case ast.Int                   => sorts.Int
      case ast.Bool                  => sorts.Bool
      case ast.Perm                  => sorts.Perm
      case ast.Ref                   => sorts.Ref
      case ast.SeqType(elementsType) => sorts.Seq(typeToSort(elementsType))
    }
  }

  def mapHeapToStore(
      store: Store,
      heap: ExtractedHeap,
      model: Model
  ): ExtractedModel = {
    var map: Map[String, ExtractedModelEntry] = Map()
    val nullRefName: String = model.entries("$Ref.null").toString
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
      println(s"Debug (mapping): $term")
      val termEval = evaluateTerm(term, model)
      val entry =
        mapLocalVar(localtype, termEval, heap, model, List(), nullRefName)
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
  def extractedHeap: ExtractedHeap =
    Converter.extractHeap(heap, model)
  def extractedHeaps: Map[String, ExtractedHeap] =
    oldHeaps.map(x => x._1 -> Converter.extractHeap(x._2.values, model))

  def extractedModel = Converter.mapHeapToStore(store, extractedHeap, model)

  def modelAtLabel: Map[String, ExtractedModel] = extractedHeaps.map(x =>
    (x._1 -> Converter.mapHeapToStore(store, x._2, model))
  )
}
