// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package viper.silicon.reporting

import viper.silicon

import scala.util.{Success, Try}
import viper.silver.verifier.{ApplicationEntry, ConstantEntry, MapEntry, Model, ModelEntry, ValueEntry}
import viper.silver.ast
import viper.silicon.Map
import viper.silicon.interfaces.state.Chunk
import viper.silicon.resources.{FieldID, PredicateID}
import viper.silicon.state.{BasicChunk, DefaultSymbolConverter, State, Store, SymbolConverter}
import viper.silicon.{state => st}
import viper.silicon.state.terms._
import viper.silicon.decider.TermToSMTLib2Converter
import viper.silicon.interfaces.decider.TermConverter
import viper.silicon.state.terms.sorts.UserSort
import viper.silicon.state.terms.sorts.Snap
import viper.silver.utility.Common.Rational

case class ExtractedModel(entries: Map[String, ExtractedModelEntry]) {
  override lazy val toString: String =
    entries.map { case (name, entry) => s"$name <- ${entry.toString}" }.mkString("\n")
}

sealed trait ExtractedModelEntry {
  def asValueEntry: ValueEntry
  def toString: String
}

// classes for extracted Model Entries
case class LitIntEntry(value: BigInt) extends ExtractedModelEntry {
  override lazy val toString: String = value.toString
  lazy val asValueEntry: ValueEntry = {
    if (value < 0) {
      ApplicationEntry("-", Seq(ConstantEntry((-value).toString)))
    } else {
      ConstantEntry(value.toString)
    }
  }
}

case class LitBoolEntry(value: Boolean) extends ExtractedModelEntry {
  override lazy val toString: String = value.toString
  lazy val asValueEntry: ValueEntry = ConstantEntry(value.toString)
}

case class LitPermEntry(value: Rational) extends ExtractedModelEntry {
  override lazy val toString: String = value.toString
  lazy val asValueEntry: ValueEntry = ConstantEntry(value.toString)
}

case class RefEntry(name: String,
                    fields: Map[String, (ExtractedModelEntry, Option[Rational])])
  extends ExtractedModelEntry {
  override lazy val toString: String = {
    val buf = fields
      .map(x =>
        s"\t${x._1}(perm: ${x._2._2.map(_.toString).getOrElse("?")}) <- ${x._2._1.toString.split("\n").mkString("\n\t")}\n"
      )
      .mkString("")
    s"Ref ($name) {\n$buf}"
  }
  lazy val asValueEntry: ValueEntry = ConstantEntry(name)
}

case class NullRefEntry(name: String) extends ExtractedModelEntry {
  override lazy val toString = s"Null($name)"
  lazy val asValueEntry: ValueEntry = ConstantEntry(name)
}

case class RecursiveRefEntry(name: String) extends ExtractedModelEntry {
  override lazy val toString = s"recursive reference to $name"
  lazy val asValueEntry: ValueEntry = ConstantEntry(name)
}

case class VarEntry(name: String, sort: Sort) extends ExtractedModelEntry {
  override lazy val toString: String = name
  lazy val asValueEntry: ValueEntry = ConstantEntry(name)
}

case class OtherEntry(value: String, problem: String = "") extends ExtractedModelEntry {
  override lazy val toString = s"$value [$problem]"
  lazy val asValueEntry: ValueEntry = ConstantEntry(value)
}

case class SeqEntry(name: String, values: Vector[ExtractedModelEntry]) extends ExtractedModelEntry {
  override lazy val toString = s"($name): [${values.map(_.toString).mkString(", ")}]"
  lazy val asValueEntry: ValueEntry = ConstantEntry(name)
}
case class SetEntry(name: String, values: Set[ExtractedModelEntry]) extends ExtractedModelEntry {
  override lazy val toString = s"($name): {${values.map(_.toString).mkString(", ")}}"
  lazy val asValueEntry: ValueEntry = ConstantEntry(name)
}
case class MultiSetEntry(name: String, values: Map[ExtractedModelEntry, Int]) extends ExtractedModelEntry {
  override lazy val toString = s"($name): {${values.map(_.toString).mkString(", ")}}"
  lazy val asValueEntry: ValueEntry = ConstantEntry(name)
}

case class UnprocessedModelEntry(entry: ValueEntry) extends ExtractedModelEntry {
  override lazy val toString = s"$entry"
  lazy val asValueEntry: ValueEntry = entry
}

// processed Heap representation:
sealed trait HeapEntry {
  def toString: String
}

case class ExtractedHeap(entries: Vector[HeapEntry])

case class PredHeapEntry(name: String,
                         args: Seq[ExtractedModelEntry],
                         perm: Option[Rational] = None)
  extends HeapEntry with ExtractedModelEntry {
  override lazy val toString = s"acc($name(${args.mkString(", ")})), ${perm.getOrElse("?")}"
  lazy val asValueEntry: ValueEntry = ConstantEntry(name)
}

case class FieldHeapEntry(recv: VarEntry,
                          field: String,
                          perm: Option[Rational],
                          sort: Sort,
                          entry: ExtractedModelEntry)
  extends HeapEntry {
  override lazy val toString = s"acc($recv.$field), ${perm.getOrElse("?")}"
}

case class FVFEntry(fvf: ExtractedModelEntry,
                    field: String,
                    values: (Map[VarEntry, ExtractedModelEntry], ExtractedModelEntry),
                    perms: (Map[VarEntry, Option[Rational]], Option[Rational]),
                    sort: Sort)
  extends HeapEntry {
  override lazy val toString = s"FVF_$field{$values , $perms}"
}

case class UnresolvedHeapEntry(chunk: Chunk, reason: String) extends HeapEntry {
  override lazy val toString = s"$chunk (not further processed because: $reason)"
}

object Converter {
  lazy val termconverter: TermConverter[String, String, String] = {
    val conv = new TermToSMTLib2Converter()
    conv.start()
    conv
  }
  lazy val symbolConverter: SymbolConverter = new DefaultSymbolConverter
  //some tokens used for naming model entries in a more maintainable way
  lazy val snapUnitId: String = termconverter.convert(Unit)
  lazy val nullRefId: String = termconverter.convert(Null)

  def getFunctionValue(model: Model,
                       fname: String,
                       args: Seq[ValueEntry],
                       toSort: Sort
                      ): ExtractedModelEntry = {
    val entry: Option[ModelEntry] = model.entries.get(fname)
    entry match {
      case Some(MapEntry(m, els)) => getConstantEntry(toSort, m.getOrElse(args, els))
      case Some(m)                => getConstantEntry(toSort, m)
      case None                   => OtherEntry(fname, "function not found in model")
    }
  }

  def getConstantEntry(s: Sort, m: ModelEntry): ExtractedModelEntry = {
    //unspecified case if z3 is called with option "model.partial=true"
    m match { 
      case ConstantEntry("#unspecified") => return OtherEntry("#unspecified", "default case")
      case _ => ()
    }
    s match {
      case sorts.Ref => VarEntry(m.toString, sorts.Ref)
      case sorts.Int =>
        m match {
          case ConstantEntry(x)             => LitIntEntry(BigInt(x))
          case ApplicationEntry(name, args) =>
            // this is needed because negative integers are stored as ApplicationEntries
            val res = getConstantEntry(s, args.head)
            (res, name) match {
              case (LitIntEntry(x), "-") => LitIntEntry(-x)
              case _                     => OtherEntry(m.toString, "not an integer literal")
            }
          case _ => OtherEntry(m.toString, "not an integer literal")
        }
      case sorts.Bool =>
        m match {
          case ConstantEntry("true")  => LitBoolEntry(true)
          case ConstantEntry("false") => LitBoolEntry(false)
          case ConstantEntry("0") => LitBoolEntry(false) // this is kind of hacky but there is some strangeness happening...
          case ConstantEntry("1") => LitBoolEntry(true)
          case ApplicationEntry(_, arguments) => getConstantEntry(s, arguments.head) // sometimes bools are represented by application("=", application("var",0))
          case _ => OtherEntry(m.toString, "not a boolean literal")
        }
      case sorts.Seq(_) 
        | sorts.Set(_)
        // | sorts.Map(_)
        // | sorts.Multiset(_)
        =>
        // entry will be resolved on demand, i.e. when calling `extractVal` in the converter
        // thus, we avoid dealing with recursive Refs and avoid evaluation functions at this stage
        VarEntry(m.toString, s)
      case sorts.Perm =>
        m match {
          case ConstantEntry(x) =>
            val rational = x.toDouble match {
              case 0.0 => Rational.zero
              case 1.0 => Rational.one
              case x =>
                val intVal = x.toInt
                val decimal = x - intVal
                Rational(intVal, 1) + Rational(1, (1/decimal).toInt)
            }
            LitPermEntry(rational)
          case ApplicationEntry(name, args) =>
            val res = getConstantEntry(s, args.head)
            (res, name) match {
              case (LitPermEntry(x), "-") => LitPermEntry(-x)
              case (_, "/") =>  (getConstantEntry(s, args.head), getConstantEntry(s, args.drop(1).head)) match {
                case (LitPermEntry(x), LitPermEntry(y)) => LitPermEntry(x/y)
                case _ => OtherEntry(m.toString, "not a permission literal div")
              }
              case _ => OtherEntry(m.toString, "not a permission literal")
            }
          case _ => OtherEntry(m.toString, "not a permission literal")
        }
      case sorts.UserSort(id) => 
        m match {
          // TODO: remove this string-based operation
          case ConstantEntry(v) => DomainValueEntry(id.toString, v.split("!").last)
          case _ => OtherEntry(id.toString,"not a constant entry---")
        }
      //ISSUE: snap types are translated to domain sorts
      /* case sorts.Snap =>
        m match {
          case ConstantEntry(value) => DomainValueEntry(value, s.toString()) // we just make a snap domain i guess
          case ApplicationEntry(name, args) => OtherEntry(s.toString(), s"app$name $args snap not a constant")
          case MapEntry(o, d) => OtherEntry(s.toString(), s"map snap not a constant")
          case _ => OtherEntry(s.toString(), s"snap not a constant")
        } */
      case _ =>
        m match {
          case e: ValueEntry => UnprocessedModelEntry(e)
          case e: MapEntry => OtherEntry(e.toString, "MapEntry instead of Constant")
        }
    }
  }

  def evaluateTerm(term: Term, model: Model): ExtractedModelEntry = {
    term match {
      case Unit              => UnprocessedModelEntry(ConstantEntry(snapUnitId))
      case IntLiteral(x)     => LitIntEntry(x)
      case t: BooleanLiteral => LitBoolEntry(t.value)
      case Null              => VarEntry(model.entries(nullRefId).toString, sorts.Ref)
      case Var(_, sort, _) =>
        val key: String = term.toString
        val entry: Option[ModelEntry] = model.entries.get(key)
        entry
          .map(x => getConstantEntry(sort, x))
          .getOrElse(OtherEntry(term.toString, "variable not found in model"))

      case App(app, args) =>
        // TODO: replace these String literals generated by other parts of silicon
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
          case OtherEntry(t, m) => OtherEntry(s"Second($t)$m", "unapplicable")
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
        getFunctionValue(model, lookupFuncName, arg, sorts.Snap)
      case _ => OtherEntry(term.toString, "unhandled")
    }
  }

  def extractHeap(h: Iterable[Chunk], model: Model): ExtractedHeap = {
    var entries: Vector[HeapEntry] = Vector()
    h foreach {
      case c @ BasicChunk(FieldID, _, _, _, _, _, _, _) =>
        val entry = extractField(c, model)
        entries = entries :+ entry
      case c @ BasicChunk(PredicateID, _, _, _, _, _, _, _) =>
        val entry = extractPredicate(c, model)
        entries = entries :+ entry
      case c: BasicChunk =>
        entries = entries :+ UnresolvedHeapEntry(c, "Magic Wands not supported")
      case c: st.QuantifiedFieldChunk => 
        val entry = c.snapshotMap
        val fvf = evaluateTerm(entry, model)
        val fieldname = c.id.name 
       
        try { // many things can go wrong but if they do, we cannot infer anything anyways
          val recvsort = c.singletonRcvr.get.sort
          val receivers = (0 to 10).map(x => VarEntry(s"$$Ref!val!$x", recvsort))
          val recv = VarEntry("$Ref!val!0", sorts.Ref)
          val fieldsort = c.fvf.sort.asInstanceOf[sorts.FieldValueFunction].codomainSort
          val permission = getFunctionValue(model, s"$$FVF.perm_$fieldname", Seq(fvf.asValueEntry, recv.asValueEntry), sorts.Perm)
          val values = receivers map (x => getFunctionValue(model, s"$$FVF.lookup_$fieldname", Seq(fvf.asValueEntry, x.asValueEntry), fieldsort))
          entries = entries ++ values.zip(receivers).map(x => FieldHeapEntry(x._2, fieldname, Some(permission.asInstanceOf[LitPermEntry].value), fieldsort, x._1))
        } catch {
          case _: Throwable => // continue
        }
      case _: st.QuantifiedPredicateChunk => // it seems that sometimes QPs do occur but not deterministically... :)

      case c =>
        entries = entries :+ UnresolvedHeapEntry(c, "Non-basic chunks not supported")
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
      // if there are other types of values for permissions they should be added here
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
    // this might be too simple for some cases but for prusti to tell if some
    // variable is part of a class it should be good enough
    // not really sure if the snap value should be added, seems to be same as one of
    // the args in most cases.
    
    val argsEval = chunk.args.map(x => evaluateTerm(x, model))
    val perm: Option[Rational] = evalPerm(chunk.perm, model)
    PredHeapEntry(chunk.id.toString, argsEval, perm)
  }

  def evalPerm(value: Term, model: Model): Option[Rational] = {
    value match {
      case _: Var => evaluateTerm(value, model) match {
        case LitPermEntry(value) => Some(value)
        case _ => None
      }
      case App(_, _) => None
      case NoPerm => Some(Rational.zero)
      case FullPerm => Some(Rational.one)
      case FractionPermLiteral(r) => Some(r)
      case _: FractionPerm => None
      case IsValidPermVal(_) => None
      case IsReadPermVar(_) => None
      case PermTimes(v1, v2) =>
        evalPerm(v1, model).flatMap(x => evalPerm(v2, model).map(y => x * y))
      case IntPermTimes(v1, v2) =>
        evalPerm(v1, model).flatMap(x => evalPerm(v2, model).map(y => x * y))
      case PermIntDiv(v1, v2) =>
        evalPerm(v1, model).flatMap(x => evalPerm(v2, model).map(y => x / y))
      case PermPlus(v1, v2) =>
        evalPerm(v1, model).flatMap(x => evalPerm(v2, model).map(y => x + y))
      case PermMinus(v1, v2) =>
        evalPerm(v1, model).flatMap(x => evalPerm(v2, model).map(y => x - y))
      case PermLess(_, _) => None
      case PermAtMost(_, _) => None
      case PermMin(_, _) => None
      case _ => None
    }
  }

  def extractSequence(model: Model,
                      heap: ExtractedHeap,
                      nullRefName: String,
                      name: String,
                      elementSort: Sort,
                      encountered: Set[String]
                     ): ExtractedModelEntry = {
    if (!encountered.contains(name)) {
      val newEncountered = encountered + name
      // hopefully Seq_len can only contain integers
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
            // valueEntry might be a Ref or Sequence and has to be mapped as well
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

  def extractSet(model: Model,
                 name: String,
                 elementSort: Sort
                ): ExtractedModelEntry = {
    val lenTry: Try[Int] = Try(
        getFunctionValue(
          model,
          "Set_card",
          Seq(ConstantEntry(name)),
          sorts.Int
        ).asInstanceOf[LitIntEntry].value.toInt
      )
    SetEntry(name, Range.apply(0, lenTry.getOrElse(0)).map(x => getSomeEntry(elementSort, x)).toSet)
  }

  def getSomeEntry(sort: Sort, num: Int): ExtractedModelEntry = sort match {
    case sorts.Bool => LitBoolEntry(num % 2 == 0)
    case sorts.Int => LitIntEntry(num)
    case UserSort(id) => DomainValueEntry(id.toString, num.toString)
    case x => VarEntry(s"${x.id.toString.replace("[","<").replace("]",">")}!val!$num" , sort)
  }

  def mapLocalVar(sort: Option[Sort],
                  termEval: ExtractedModelEntry,
                  heap: ExtractedHeap,
                  model: Model,
                  encountered: Set[String],
                  nullRefName: String
                 ): ExtractedModelEntry = {
    val name = termEval.toString
    sort match {
      case Some(sorts.Int) => termEval
      case Some(sorts.Bool) => termEval
      case Some(sorts.Ref) =>
        var map: Map[String, (ExtractedModelEntry, Option[Rational])] = Map()
        // if Sort is Ref then termEval has to be of type VarEntry (?)

        // this list helps to recognize and handle cyclic references
        if (name == nullRefName) {
          NullRefEntry(name)
        } else if (!encountered.contains(name)) {
          val newEncountered = encountered + name
          for (entry: HeapEntry <- heap.entries) {
            entry match {
              case FieldHeapEntry(recv, field, perm @ _, sort, value) =>
                if (termEval == recv) {
                  val recEntry = mapLocalVar(Some(sort), value, heap, model, newEncountered, nullRefName)
                  map += (field -> (recEntry, perm))
                }
              case FVFEntry(_, field, values, perms, sort) =>
                val recEntry = mapLocalVar(
                  Some(sort),
                  values._1.getOrElse(termEval.asInstanceOf[VarEntry], values._2),
                  heap,
                  model,
                  newEncountered,
                  nullRefName
                )
                val perm = perms._1.getOrElse(termEval.asInstanceOf[VarEntry], perms._2)
                map += (field -> (recEntry, perm))
                  
              case _ => 
            }
          }
          RefEntry(name, map)
        } else {
          RecursiveRefEntry(name)
        }

      case Some(sorts.Seq(elementSort)) =>
        extractSequence(model, heap, nullRefName, name, elementSort, encountered)

      case Some(sorts.Set(elementSort)) => extractSet(model, name, elementSort)
      case Some(sorts.UserSort(_)) => termEval
      case _ => termEval
    }
  }

  def typeToSort(typ: ast.Type): Option[Sort] = {
    // if this returns None, we can still try to evaluate the model entry
    try {
      Some(symbolConverter.toSort(typ)) // simplify the logic with this
    } catch {
      case _: Throwable => None
    }
  }

  def mapHeapToStore(store: Store,
                     heap: ExtractedHeap,
                     model: Model
                    ): ExtractedModel = {
    var map: Map[String, ExtractedModelEntry] = Map()
    val nullRefName: String = model.entries.getOrElse("$Ref.null","Ref!val!0").toString
    for ((variable: ast.AbstractLocalVar, term: Term) <- store.termValues) {
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


  /**
    * extracts domains from a program. only the ones that are used in the program... no generics
    * it also extracts all instances (translates the generics to concrete values)
    */
  def getDomains(model: Model, program: ast.Program): Seq[DomainEntry] = {
    val domains = program.collect {
      case a: ast.Domain => a
    }
    val concreteDoms = program.collect { // find all definitive type instances
      case ast.DomainType(n, map) => (n, map)
      case d: ast.DomainFuncApp => (d.domainName, d.typVarMap) // sometimes we use a function without having an actual member of this...

    }.filterNot(x => containsTypeVar(x._2.values.toSeq)).toSet // make sure we have all possible mappings without duplicates
    
    val doms = domains.flatMap(x => if(x.typVars == Nil) Seq((x, Map.empty[ast.TypeVar, ast.Type])) else concreteDoms.filter(_._1 == x.name).map(y =>(x, silicon.toMap(y._2)))) // changing the typevars to the actual ones
    
    doms.map(x => {
      val types = try {
        x._1.typVars.map(x._2)
      } catch {
        case _: Throwable => Seq()
      }
      val translatedFunctions = x._1.functions.map(y => translateFunction(model, y, x._2, program))
      DomainEntry(x._1.name, types, translatedFunctions)
    }).toSeq
  }

  def containsTypeVar(s: Seq[ast.Type]): Boolean = s.exists(x => x.isInstanceOf[ast.TypeVar])

  // extract all non domain internal functions
  def getFunctions(model: Model, program: ast.Program): Seq[ExtractedFunction] = {
    val funcs = program.collect {
      case f: ast.Function => f
    }
    funcs.map(x => translateFunction(model, x, silicon.toMap(Nil), program)).toSeq
  }

  def errorfunc(problem: String): ExtractedFunction =
    ExtractedFunction("ERROR", Seq(), sorts.Unit, Map.empty, OtherEntry("ERROR", problem))

  /**
    * extracts the function instances by searching for the most likely match translating the values in the internal rep
    *
    * @param model
    * @param func the function to translate
    * @param genmap map of generic types to concrete types
    * @return
    */
  def translateFunction(model: Model, func: ast.FuncLike, genmap: Map[ast.TypeVar, ast.Type], program: ast.Program): ExtractedFunction = {
    def toSort(typ: ast.Type): Either[Throwable, Sort] = Try(symbolConverter.toSort(typ)).toEither
    def toSortWithSubstitutions(typ: ast.Type, typeErrorMsg: String): Either[String, Sort] = {
      toSort(typ)
        .left
        .flatMap(_ => typ match {
          case x: ast.GenericType => toSort(x.substitute(genmap)).left.map(_ => typeErrorMsg)
          case t: ast.TypeVar => toSort(genmap.apply(t)).left.map(_ => typeErrorMsg)
          case _ => Left("type not resolvable")
        })
    }

    val fname = func.name
    val resTyp: ast.Type = func.typ

    var (argSortErrors, argSort) = func.formalArgs
      .map(x => toSortWithSubstitutions(x.typ, s"typeError in arg type ${x.typ}"))
      .partitionMap(identity)
    if (argSortErrors.nonEmpty) {
      return errorfunc(s"$fname ${argSortErrors.head}")
    }

    val resSort = toSortWithSubstitutions(resTyp, s"typeError in return type $resTyp")
      .fold(err => { return errorfunc(s"$fname $err") }, identity)

    val smtfunc = func match {
      case t: ast.Function => symbolConverter.toFunction(t).id
      case t@ast.BackendFunc(_, _, _, _) => symbolConverter.toFunction(t, program).id
      case t: ast.DomainFunc => symbolConverter.toFunction(t, argSort :+ resSort, program).id
    }
    val kek = smtfunc.toString
      .replace("[", "<")
      .replace("]", ">")
      .replace(", ", "~_")
    val entries = model.entries
    val keys = entries.keys
    val modelFuncname = try {
      (keys.filter(_.contains(fname+"%limited")) ++ keys.filter(_ == fname) ++ keys.filter(_ == kek)).head
    } catch {
      case _: Throwable => return errorfunc(s"$fname model function not found")
    }
    entries.get(modelFuncname) match {
      /* A function could be either heap-dependent or heap-independent. If it is the former, each entry's first argument
        is of type snap. To align this with the function's definition, we add a new parameter to the function of type snap. 
        We identify a heap-dependent function by checking if it contains the keyword "%limited".
      */  
      case Some(MapEntry(m, els)) =>
        if (modelFuncname.contains("%limited")) {
          argSort = Seq(Snap) ++ argSort
        }
        val options: Map[Seq[ExtractedModelEntry], ExtractedModelEntry] = try {
          silicon.toMap(m.map(x => x._1.zip(argSort).map(y => getConstantEntry(y._2, y._1)) -> getConstantEntry(resSort, x._2)))
        } catch {
          case _: Throwable => Map.empty
        }
        ExtractedFunction(fname, argSort, resSort, options, getConstantEntry(resSort, els))

      case Some(ConstantEntry(t)) => ExtractedFunction(fname, argSort, resSort, Map.empty, getConstantEntry(resSort, ConstantEntry(t)))
      case Some(ApplicationEntry(n, args)) => ExtractedFunction(fname, argSort, resSort, Map.empty, getConstantEntry(resSort, ApplicationEntry(n, args)))
      case Some(x) => ExtractedFunction(fname, argSort, resSort, Map.empty, getConstantEntry(resSort, x))
      case None    => ExtractedFunction(fname, argSort, resSort, Map.empty, OtherEntry(fname, "function not found"))
    }
  }
}

case class Converter(model: Model,
                     store: Store,
                     heap: Iterable[Chunk],
                     oldHeaps: State.OldHeaps,
                     program: ast.Program) {
  lazy val extractedHeap: ExtractedHeap =
    Converter.extractHeap(heap, model)

  lazy val extractedHeaps: Map[String, ExtractedHeap] =
    oldHeaps.map(x => x._1 -> Converter.extractHeap(x._2.values, model))

  lazy val extractedModel: ExtractedModel =
    Converter.mapHeapToStore(store, extractedHeap, model)

  lazy val modelAtLabel: Map[String, ExtractedModel] = extractedHeaps.map(x =>
    x._1 -> Converter.mapHeapToStore(store, x._2, model)
  )
  lazy val domains: Seq[DomainEntry] = Converter.getDomains(model, program)
  lazy val nonDomainFunctions: Seq[ExtractedFunction] = Converter.getFunctions(model, program)
  def extractVal(x: VarEntry): ExtractedModelEntry =
    Converter.mapLocalVar(
      model = model,
      heap = extractedHeap,
      encountered = Set(),
      nullRefName = model.entries.getOrElse(Converter.nullRefId,"Ref!val!0").toString,
      termEval = x,
      sort = Some(x.sort)
    )
}

/**
 * Entry for user defined domains
 * CAREFUL: the types are included in the domain name and do not correspond directly to the name of a DomainEntry
 * rather they correspond to the valueName in the DomainEntry
 */
case class DomainValueEntry(domain: String, id: String) extends ExtractedModelEntry {
  def asValueEntry: ValueEntry = ConstantEntry(toString)
  override def toString: String = s"${domain}_$id"
  def getDomainName: String = domain.takeWhile(_!='[')
}

/**
  * same as DomainValueEntry but with some information about functions defined on this domain an their corresponding
  * result when using original as input for the function
  */
case class ExtendedDomainValueEntry(original: DomainValueEntry, info: Map[ExtractedFunction, ExtractedModelEntry]) extends ExtractedModelEntry {
	def asValueEntry: ValueEntry = original.asValueEntry
	override def toString: String =
    original.toString ++" where " ++ info.map(infoEntryToString).mkString("{\n\t",";\n\t","\n\t}")

  private def infoEntryToString(entry: (ExtractedFunction, ExtractedModelEntry)): String =
    entry._1.fname ++ " = " ++ entry._2.toString.flatMap(y => y match {
      case '\n' => "\n\t"
      case _ => y+:""
    })
}

/**
  * Domain entry for specific types, can also be generic
  *  does not contain axioms 
  *
  * @param name Domain name in viper
  * @param types type instances or generic types
  * @param functions functions defined within the domain not includeing functions that use this domain
  */
case class DomainEntry(name: String,
                       types: Seq[ast.Type],
                       functions: Seq[ExtractedFunction]) {
  override def toString: String =
    s"domain $valueName{\n ${functions.map(_.toString()).mkString("\n")}\n}"

  val valueName: String = s"$name${printTypes()}"

  private def printTypes(): String =
    if (types.isEmpty) ""
    else types.map(printType).mkString("[",", ","]")

  private def printType(t: ast.Type): String = t match {
    case ast.TypeVar(x) => x
    case _ => t.toString()
  }
}

/**
  * Function used within or without domains 
  * CAREFUL: it will not evaluate VarEntries this has to be done via the converter or Interpreter
  * it checks the types naïvely, false positives will occur
  *
  * @param fname function name without Type Parameter since they are concrete functions
  * @param argtypes types of the arguments
  * @param returnType return type of function
  * @param options map from arguments to function value
  * @param default default value if arguments are not contained in options
  */
case class ExtractedFunction(fname: String,
                             argtypes: Seq[Sort],
                             returnType: Sort,
                             options: Map[Seq[ExtractedModelEntry], ExtractedModelEntry],
                             default: ExtractedModelEntry) {
  def apply(args: Seq[ExtractedModelEntry]): Either[ExtractedFunction, ExtractedModelEntry] = {
    val n = args.length
    val arglength = argtypes.length
    if(n == arglength) { // full application
      if(typecheck(args, argtypes))
        Right(options.getOrElse(args, default))
      else
        throw new IllegalArgumentException("false types: required "+s"$argtypes"+ " but got: "+ s"$args")
    } else {
      if(n < arglength) {
        val (subtypes, rest) = argtypes.splitAt(n)
        if (typecheck(args, subtypes)) {
          // return new function with the first n elements applied
          val name = s"${fname}_${arglength - n}"
          val simplifiedOptions = options.filter(x => x._1.take(n) == args).map(x => (x._1.drop(n) -> x._2)) // map to simpler function
          Left(ExtractedFunction(name, rest, returnType, simplifiedOptions, default))
        } else {
          throw new IllegalArgumentException(s"false types for partial application: required $subtypes but got: $args")
        }
      } else {
        throw new IllegalArgumentException(s"to many arguments for function: $fname")
      }
    }
  }

  def image: Seq[ExtractedModelEntry] = {options.values.toSeq :+ default}

  override def toString: String = {
    if (options.nonEmpty)
      s"$fname${argtypes.mkString("(", ",", ")")}:$returnType{\n" + options.map(o => "    " + o._1.mkString(" ") + " -> " + o._2).mkString("\n") + "\n    else -> " + default +"\n}"
    else
      s"$fname{\n    " + default +"\n}"
  }

  def typecheck(is: Seq[ExtractedModelEntry], should: Seq[Sort]): Boolean = {
      is.zip(should).forall(y => typecheck(y._1, y._2))
  }

  def typecheck(is: ExtractedModelEntry, should: Sort): Boolean = {
    is match {
      case LitIntEntry(_) => should == sorts.Int
      case LitBoolEntry(_) => should == sorts.Bool
      case LitPermEntry(_) => should == sorts.Perm
      case RefEntry(_, _) 
        | NullRefEntry(_)
        | RecursiveRefEntry(_) => should == sorts.Ref
      case VarEntry(_, sort) => should == sort
      case OtherEntry(_, _) => false
      case SeqEntry(_, values) => should match {
        case sorts.Seq(_) if values.isEmpty => true
        case sorts.Seq(e) => typecheck(values.head, e)
        case _ => false
      }
      case UnprocessedModelEntry(_) => false
      case DomainValueEntry(domain, _) => should.toString == domain
      case ExtendedDomainValueEntry(original, _) => typecheck(original, should)
    }
  }
}
