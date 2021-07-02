package viper.silicon.reporting

import scala.util.{Try, Success}
import viper.silver.verifier.{Model, ModelEntry, ValueEntry, ConstantEntry, ApplicationEntry, MapEntry}
import viper.silver.ast
import viper.silicon.Map
import viper.silicon.interfaces.state.Chunk
import viper.silicon.resources.{FieldID, PredicateID}
import viper.silicon.state.{Store, State, BasicChunk}
import viper.silicon.state.terms._
import viper.silicon.decider.TermToSMTLib2Converter

//Classes for extracted Model Entries
case class ExtractedModel(entries: Map[String, ExtractedModelEntry]) {
  override lazy val toString: String = {
    entries.map(x => s"${x._1} <- ${x._2.toString}").mkString("\n")
  }
}

sealed trait ExtractedModelEntry {
  def asValueEntry: ValueEntry
  def toString: String
}

case class LitIntEntry(value: BigInt) extends ExtractedModelEntry {
  override lazy val toString: String = value.toString
  lazy val asValueEntry = {
    if (value < 0) {
      ApplicationEntry("-", Seq(ConstantEntry((-value).toString)))
    } else {
      ConstantEntry(value.toString)
    }
  }
}

case class LitBoolEntry(value: Boolean) extends ExtractedModelEntry {
  override lazy val toString: String = value.toString
  lazy val asValueEntry = ConstantEntry(value.toString)
}

case class LitPermEntry(value: Double) extends ExtractedModelEntry {
  override lazy val toString: String = value.toString
  lazy val asValueEntry = {
    if (value < 0.0) {
      ApplicationEntry("-", Seq(ConstantEntry((-value).toString)))
    } else {
      ConstantEntry(value.toString)
    }
  }
}

case class RefEntry(
    name: String,
    fields: Map[String, (ExtractedModelEntry, Option[Rational])]
) extends ExtractedModelEntry {
  override lazy val toString: String = {
    val buf = fields
      .map(x =>
        s"\t${x._1}(perm: ${x._2._2.map(_.toString).getOrElse("?")}) <- ${x._2._1.toString.split("\n").mkString("\n\t")}\n"
      )
      .mkString("")
    s"Ref ($name) {\n$buf}"
  }
  lazy val asValueEntry = ConstantEntry(name)
}

case class NullRefEntry(name: String) extends ExtractedModelEntry {
  override lazy val toString = s"Null($name)"
  lazy val asValueEntry = ConstantEntry(name)
}

case class RecursiveRefEntry(name: String) extends ExtractedModelEntry {
  override lazy val toString = s"recursive reference to $name"
  lazy val asValueEntry = ConstantEntry(name)
}

case class VarEntry(name: String, sort: Sort) extends ExtractedModelEntry {
  override lazy val toString: String = name
  lazy val asValueEntry = ConstantEntry(name)
}

case class OtherEntry(value: String, problem: String = "")
    extends ExtractedModelEntry {
  override lazy val toString = s"$value [$problem]"
  lazy val asValueEntry = ConstantEntry(value)
}

case class SeqEntry(name: String, values: Vector[ExtractedModelEntry])
    extends ExtractedModelEntry {
  override lazy val toString = s"($name): [${values.map(_.toString).mkString(", ")}]"
  lazy val asValueEntry = ConstantEntry(name)
}

case class UnprocessedModelEntry(entry: ValueEntry)
    extends ExtractedModelEntry {
  override lazy val toString = s"$entry"
  lazy val asValueEntry = entry
}

// processed Heap representation:
sealed trait HeapEntry {
  def toString: String
}

case class ExtractedHeap(entries: Vector[HeapEntry])

case class PredHeapEntry(
    name: String,
    args: Seq[ExtractedModelEntry]
) extends HeapEntry {
  override lazy val toString = s"$name(${args.mkString(", ")})"
}
case class FieldHeapEntry(
    recv: VarEntry,
    field: String,
    perm: Option[Rational],
    sort: Sort,
    entry: ExtractedModelEntry
) extends HeapEntry {
  override lazy val toString = s"$recv.$field"
}

case class UnresolvedHeapEntry(chunk: Chunk, reason: String) extends HeapEntry {
  override lazy val toString = s"$chunk (not further processed because: $reason)"
}

object Converter {
  lazy val termconverter = {
    val conv = new TermToSMTLib2Converter()
    conv.start()
    conv
  }
  //some tokens used for naming model entries in a more maintainable way
  lazy val snapUnitId: String = termconverter.convert(Unit)
  lazy val nullRefId: String = termconverter.convert(Null())

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
      case None    => OtherEntry(s"${fname}", "function not found in model")
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
            (res, name) match {
              case (LitIntEntry(x), "-") => LitIntEntry(-x)
              case _                     => OtherEntry(s"$m", "not an integer literal")
            }
          case _ => OtherEntry(s"$m", "not an integer literal")
        }
      case sorts.Bool =>
        m match {
          case ConstantEntry("true")  => LitBoolEntry(true)
          case ConstantEntry("false") => LitBoolEntry(false)
          case _ => OtherEntry(s"$m", "not a boolean literal")
        }
      case sorts.Seq(_) => VarEntry(m.toString, s) // will be resolved later
      case sorts.Perm =>
        m match {
          case ConstantEntry(x) => LitPermEntry(x.toDouble)
          case ApplicationEntry(name, args) =>
            val res = getConstantEntry(s, args.head)
            (res, name) match {
              case (LitPermEntry(x), "-") => LitPermEntry(-x)
              case _                      => OtherEntry(s"$m", "not a permission literal")
            }
          case _ => OtherEntry(s"$m", "not a permission literal")
        }
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
      case Unit              => UnprocessedModelEntry(ConstantEntry(snapUnitId))
      case IntLiteral(x)     => LitIntEntry(x)
      case t: BooleanLiteral => LitBoolEntry(t.value)
      case Null()            => VarEntry(model.entries(nullRefId).toString, sorts.Ref)
      case Var(_, sort) =>
        val key: String = term.toString
        val entry: Option[ModelEntry] = model.entries.get(key)
        entry
          .map(x => getConstantEntry(sort, x))
          .getOrElse(
            OtherEntry(s"$term", "variable not found in model")
          )

      case App(app, args) =>
        //TODO: replace these String literals generated by other parts of silicon
        // once they are directly available (e.g. from TermToSMTLib2Converter)
        // also in several other places
        var fname = s"${app.id}%limited"
        if (!model.entries.contains(fname)) {
          fname = app.id.toString
          if (!model.entries.contains(fname)) {
            fname = fname.replace("[", "<").replace("]", ">")
          }
        }
        val toSort = app.resultSort
        val argEntries: Seq[ExtractedModelEntry] = args
          .map(t => evaluateTerm(t, model))

        val argsFinal = argEntries.map {
          case UnprocessedModelEntry(entry) => entry
          case e: ExtractedModelEntry       => ConstantEntry(e.toString)
        }
        getFunctionValue(model, fname, argsFinal, toSort)

      case Combine(p0, p1) =>
        val p0Eval = evaluateTerm(p0, model).asValueEntry
        val p1Eval = evaluateTerm(p1, model).asValueEntry
        val entry = ApplicationEntry("$Snap.combine", Seq(p0Eval, p1Eval))
        UnprocessedModelEntry(entry)

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
        val fromSortName: String = termconverter.convert(t.sort)
        val toSortName: String = termconverter.convert(to)
        val fname = s"$$SortWrappers.${fromSortName}To$toSortName"

        sub match {
          case UnprocessedModelEntry(entry) =>
            getFunctionValue(model, fname, Seq(entry), to)
          case OtherEntry(t, _) =>
            OtherEntry(s"SortWrapper($t)", "unapplicable")
          case _ => OtherEntry(s"SortWrapper($t)", "unapplicable")
        }

      case PredicateLookup(predname, psf, args) =>
        val lookupFuncName: String = s"$$PSF.lookup_$predname"
        val snap = toSnapTree.apply(args)
        val snapVal = evaluateTerm(snap, model).asValueEntry
        val psfVal = evaluateTerm(psf, model).asValueEntry
        val arg = Seq(psfVal, snapVal)
        val result = getFunctionValue(model, lookupFuncName, arg, sorts.Snap)
        result

      case _ =>
        OtherEntry(s"$term", "unhandled")
    }
  }

  def extractHeap(h: Iterable[Chunk], model: Model): ExtractedHeap = {
    var entries: Vector[HeapEntry] = Vector()
    h foreach {
      case c @ BasicChunk(FieldID, _, _, _, _) =>
        val entry = extractField(c, model)
        entries = entries :+ entry
      case c @ BasicChunk(PredicateID, _, _, _, _) =>
        val entry = extractPredicate(c, model)
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
      encountered: Set[String]
  ): ExtractedModelEntry = {
    if (!encountered.contains(name)) {
      val newEncountered = encountered + name
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
          var values: Vector[ExtractedModelEntry] = Vector()
          for (i <- 0 until len) {
            val valueEntry: ExtractedModelEntry = getFunctionValue(
              model,
              "Seq_index",
              Seq(ConstantEntry(name), ConstantEntry(i.toString)),
              elementSort
            )
            //valueEntry might be a Ref or Sequence and has to be mapped as well
            val finalEntry: ExtractedModelEntry = mapLocalVar(
              Some(elementSort),
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
      sort: Option[Sort],
      termEval: ExtractedModelEntry,
      heap: ExtractedHeap,
      model: Model,
      encountered: Set[String],
      nullRefName: String
  ): ExtractedModelEntry = {
    val name = termEval.toString
    sort match {
      case Some(sorts.Int)  => termEval
      case Some(sorts.Bool) => termEval
      case Some(sorts.Ref) =>
        var map: Map[String, (ExtractedModelEntry, Option[Rational])] = Map()
        //if Sort is Ref then termEval has to be of type VarEntry (?)

        //this list helps to recognize and handle cyclic references
        if (name == nullRefName) {
          NullRefEntry(name)
        } else if (!encountered.contains(name)) {
          val newEncountered = encountered + name
          for (entry: HeapEntry <- heap.entries) {
            entry match {
              case FieldHeapEntry(recv, field, perm @ _, sort, value) =>
                if (termEval == recv) {
                  val recEntry =
                    mapLocalVar(
                      Some(sort),
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
      case Some(sorts.Seq(elementSort)) =>
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

  def typeToSort(typ: ast.Type): Option[Sort] = {
    //If this returns None, we can still try to evaluate the model entry
    typ match {
      case ast.Int  => Some(sorts.Int)
      case ast.Bool => Some(sorts.Bool)
      case ast.Perm => Some(sorts.Perm)
      case ast.Ref  => Some(sorts.Ref)
      case ast.SeqType(elementsType) =>
        val elementSort = typeToSort(elementsType)
        elementSort.map(x => sorts.Seq(x))
      case _ => None
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
      var localSort: Option[Sort] = None
      val name = variable match {
        case ast.LocalVar(n, typ) =>
          localSort = typeToSort(typ)
          n
        case ast.Result(typ) =>
          localSort = typeToSort(typ)
          "Result()"
      }
      val termEval = evaluateTerm(term, model)
      val entry =
        mapLocalVar(localSort, termEval, heap, model, Set(), nullRefName)
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
