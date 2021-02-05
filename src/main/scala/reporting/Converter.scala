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
  override def toString: String = value.toString
  def negate: LitIntEntry = LitIntEntry(-value)
}
case class LitBoolEntry(value: Boolean) extends ExtractedModelEntry {
  override def toString: String = value.toString
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
  override def toString: String = name
}

case class OtherEntry(value: String, problem: String = "")
    extends ExtractedModelEntry {
  override def toString = s"$value [$problem]"
}
case class SeqEntry(name: String, values: List[ExtractedModelEntry])
    extends ExtractedModelEntry {
  override def toString = s"($name): [${values.map(_.toString).mkString(", ")}]"
}

case class UnprocessedModelEntry(entry: ValueEntry)
    extends ExtractedModelEntry {
  override def toString = s"$entry"
}

// processed Heap representation:
sealed trait HeapEntry

case class ExtractedHeap(entries: List[HeapEntry])

case class PredHeapEntry(
    name: String,
    args: Seq[ExtractedModelEntry]
) extends HeapEntry {
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
        getConstantEntry(toSort, m.getOrElse(args, els))
      case Some(m) => getConstantEntry(toSort, m)
      case None    => OtherEntry("${fname}", "function not found in model")
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
          case ConstantEntry(x)             => LitIntEntry(BigInt(x))
          case ApplicationEntry(name, args) =>
            //this is needed because negative integers are stored as ApplicationEntries
            val res = getConstantEntry(s, args.head)
            res match {
              case l @ LitIntEntry(_) =>
                if (name == "-") {
                  l.negate
                } else {
                  //are there other special cases for integers?
                  OtherEntry(s"$m", "ApplicationEntry instead of constant")
                }
              case _ =>
                OtherEntry(s"$m", "not an integer literal")
            }
          case _ => OtherEntry(s"$m", "not an integer literal")
        }
      case sorts.Bool =>
        m.toString.toLowerCase() match {
          case "true"  => LitBoolEntry(true)
          case "false" => LitBoolEntry(false)
          case x =>
            OtherEntry(s"$x", "not a boolean literal")
        }
      case sorts.Seq(_) => VarEntry(m.toString, s) // will be resolved later
      case _ =>
        m match {
          case e: ValueEntry => UnprocessedModelEntry(e)
          case e: MapEntry =>
            OtherEntry(s"$e", "MapEntry instead of Constant")
        }
    }
  }

  def evaluateTerm(term: Term, model: Model): ExtractedModelEntry = {
    term match {
      case Unit              => UnprocessedModelEntry(ConstantEntry("$Snap.unit"))
      case IntLiteral(x)     => LitIntEntry(x)
      case t: BooleanLiteral => LitBoolEntry(t.value)
      case Null()            => VarEntry(model.entries("$Ref.null").toString, sorts.Ref)
      case Var(_, sort) =>
        val key: String = term.toString
        val entry: Option[ModelEntry] = model.entries.get(key)
        entry
          .map(x => getConstantEntry(sort, x))
          .getOrElse(
            OtherEntry(s"$term", "variable not found in model")
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
        println("DEBUG: App encountered")
        getFunctionValue(model, fname, argEntries, toSort)

      case Combine(p0, p1) =>
        //assuming Combine can only contain other snap.combine and snap.unit
        val p0Eval = evaluateTerm(p0, model)
        val p1Eval = evaluateTerm(p1, model)
        val e0Try = Try(p0Eval.asInstanceOf[UnprocessedModelEntry].entry)
        val e1Try = Try(p1Eval.asInstanceOf[UnprocessedModelEntry].entry)
        (e0Try, e1Try) match {
          case (Success(e0), Success(e1)) =>
            val entry = ApplicationEntry("$Snap.combine", Seq(e0, e1))
            UnprocessedModelEntry(entry)
          case _ => OtherEntry(s"$term", "unhandled argument terms")
        }

      case First(p) =>
        val sub = evaluateTerm(p, model)
        sub match {
          case UnprocessedModelEntry(ApplicationEntry(name, args)) =>
            if (name == "$Snap.combine") {
              UnprocessedModelEntry(args.head)
            } else {
              OtherEntry(s"First($p)", "unapplicable")
            }
          case OtherEntry(t, _) => OtherEntry(s"First($t)", "unapplicable")
          case _                => OtherEntry(s"First($sub)", "unapplicable")
        }

      case Second(p) =>
        val sub = evaluateTerm(p, model)
        sub match {
          case UnprocessedModelEntry(ApplicationEntry(name, args)) =>
            if (name == "$Snap.combine") {
              UnprocessedModelEntry(args(1))
            } else {
              OtherEntry(s"Second($p})", "unapplicable")
            }
          case OtherEntry(t, _) => OtherEntry(s"Second($t)", "unapplicable")
          case _                => OtherEntry(s"Second($sub)", "unapplicable")
        }

      case SortWrapper(t, to) =>
        val sub = evaluateTerm(t, model)
        val fromSortName: String = translateSort(t.sort)
        val toSortName: String = translateSort(to)
        val fname = s"$$SortWrappers.${fromSortName}To$toSortName"

        sub match {
          case UnprocessedModelEntry(entry) =>
            getFunctionValue(model, fname, Seq(entry), to)
          case OtherEntry(t, _) =>
            OtherEntry(s"SortWrapper($t)", "unapplicable")
          case _ => OtherEntry(s"SortWrapper($t)", "unapplicable")
        }

      case PredicateLookup(predname, _, _) =>
        /* not tested! did never occurr in considered examples */
        /* val lookupFuncName: String = s"$$PSF.lookup_$predname"
        val snap = toSnapTree.apply(args)
        val psfVal = evaluateTerm(psf, model)
        val snapVal = evaluateTerm(snap, model) */
        //getFunctionValue(model, lookupFuncName, arg)
        OtherEntry(s"PredicateLookup($predname)", "unhandled")

      case _ =>
        OtherEntry(s"$term", "unhandled")
    }
  }

  def extractHeap(h: Iterable[Chunk], model: Model): ExtractedHeap = {
    var entries: List[HeapEntry] = List()
    h foreach {
      case c @ BasicChunk(FieldID, _, _, _, _) =>
        val entry = extractField(c, model)
        entries = entries :+ entry
        println(s"DEBUG (heap field): $entry")
      case c @ BasicChunk(PredicateID, _, _, _, _) =>
        val entry = extractPredicate(c, model)
        println(s"DEBUG (heap predicate): $entry")
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
      //if there are other types of values for permissions they should be added here
      case _ => None
    }
    val value = evaluateTerm(chunk.snap, model)
    println(s"DEBUG field value: $value")
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

  def extractPredicate(chunk: BasicChunk, model: Model): HeapEntry = {
    //this might be too simple for some cases but for prusti to tell if some
    //variable is part of a class it should be good enough
    //not really sure if the snap value should be added, seems to be same as one of
    //the args in most cases.
    val argsEval = chunk.args.map(x => evaluateTerm(x, model))
    val entry = PredHeapEntry(chunk.id.toString, argsEval)
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
  lazy val extractedHeap: ExtractedHeap =
    Converter.extractHeap(heap, model)

  lazy val extractedHeaps: Map[String, ExtractedHeap] =
    oldHeaps.map(x => x._1 -> Converter.extractHeap(x._2.values, model))

  lazy val extractedModel: ExtractedModel =
    Converter.mapHeapToStore(store, extractedHeap, model)

  lazy val modelAtLabel: Map[String, ExtractedModel] = extractedHeaps.map(x =>
    x._1 -> Converter.mapHeapToStore(store, x._2, model)
  )
}
