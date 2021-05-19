package viper.silicon.reporting

import scala.util.{Try, Success}
import viper.silver.verifier.{Model, ModelEntry, ValueEntry, ConstantEntry, ApplicationEntry, MapEntry}
import viper.silver.ast
import viper.silicon.interfaces.state.Chunk
import viper.silicon.resources.{FieldID, PredicateID}
import viper.silicon.state.{Store, State, BasicChunk,SymbolConverter,DefaultSymbolConverter}
import viper.silicon.{state => st}
import viper.silicon.state.terms._
import viper.silicon.decider.TermToSMTLib2Converter
import _root_.javax.print.attribute.standard.MediaSize.Other


//Classes for extracted Model Entries
case class ExtractedModel(entries: Map[String, ExtractedModelEntry]) {
  override lazy val toString: String = {
    entries.map(x => s"${x._1} <- ${x._2.toString}").mkString("\n")
  }
}

sealed trait ExtractedModelEntry{
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
  lazy val symbolConverter:SymbolConverter = new DefaultSymbolConverter
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
      case None    => OtherEntry("${fname}", "function not found in model")
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
          case ConstantEntry("0") => LitBoolEntry(false)//this is kind of hacky but there is some strangeness happening...
          case ConstantEntry("1") => LitBoolEntry(true)
          case ApplicationEntry(name, arguments) => getConstantEntry(s, arguments.head) // sometimes bools are represented by application("=", application("var",0))
          case _ => {OtherEntry(s"$m", "not a boolean literal")}
        }
      case sorts.Seq(_) => VarEntry(m.toString, s)// will be resolved later
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
      case sorts.UserSort(id) => 
        m match {
          case ConstantEntry(v) => DomainValueEntry(id.toString(),v.split("!").last)//this is a hack for the moment if there is any way to do this diffrently let me know
          case _ => OtherEntry(id.toString(),"not a constant entry---")
      }
      //ISSUE: snap types are translated to domain sorts
      /* case sorts.Snap =>
        m match {
          case ConstantEntry(value) => DomainValueEntry(value,s.toString()) // we just make a snap domain i guess
          case ApplicationEntry(name, args) => OtherEntry(s.toString(),s"app$name $args snap not a constant")
          case MapEntry(o,d) =>OtherEntry(s.toString(),s"map snap not a constant")
          case _ => OtherEntry(s.toString(),s"snap not a constant")
        } */
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
            OtherEntry(s"SortWrapper($t)o", "unapplicable")
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
        OtherEntry(s"s$term", "unhandled")
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
      case c :st.QuantifiedFieldChunk => 
        val entry = c.snapshotMap
        val fvf = evaluateTerm(entry,model)
        val fieldname = c.id.name 
        try {//many things can go wrong but if they do we cannot infer anything anyways
          val recvsort =c.singletonRcvr.get.sort
          val recievers = (0 to 10).map(x=>VarEntry(s"$$Ref!val!$x",recvsort))
          val recv =  VarEntry("$Ref!val!0",sorts.Ref)
          val fieldsort  = c.fvf.sort.asInstanceOf[sorts.FieldValueFunction].codomainSort
          val permission = getFunctionValue(model,s"$$FVF.perm_$fieldname",Seq(fvf.asValueEntry,recv.asValueEntry),sorts.Perm)
          //val domvals = getFunctionValue(model,s"$$FVF.domain_$fieldname",Seq(fvf.asValueEntry,recv.asValueEntry),sorts.Set(sorts.Ref))
        
          val values =recievers map (x=>getFunctionValue(model,s"$$FVF.lookup_$fieldname",Seq(fvf.asValueEntry,x.asValueEntry),fieldsort))
          val value = getFunctionValue(model,s"$$FVF.lookup_$fieldname",Seq(fvf.asValueEntry,recv.asValueEntry),fieldsort)
          //printf(s"${fvf},$permission,$fieldname;$value} ,${c.initialCond};\n")
          entries = entries ++ values.zip(recievers).map(x=>FieldHeapEntry(x._2,fieldname,Some(new Rational(permission.asInstanceOf[LitPermEntry].value.toInt,1)),fieldsort,x._1))
        }catch {
          case _:Throwable => ///continue
        }
        
        
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
          for (i <- 0 to len-1) {
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
      case Some(sorts.UserSort(id)) => termEval
      case _ => termEval
    }
  }

  def typeToSort(typ: ast.Type): Option[Sort] = {
    //If this returns None, we can still try to evaluate the model entry
    try{
    Some(symbolConverter.toSort(typ))// simplify the logic with this
    }catch{
      case _:Throwable => None
    }
    /* typ match {
      case ast.Int  => Some(sorts.Int)
      case ast.Bool => Some(sorts.Bool)
      case ast.Perm => Some(sorts.Perm)
      case ast.Ref  => Some(sorts.Ref)
      case ast.SeqType(elementsType) =>
        val elementSort = typeToSort(elementsType)
        elementSort.map(x => sorts.Seq(x))
      case _ => None
    } */
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


  /**
    * extracts domains from a program. only the ones that are used in the program... no generics
    * it also extracts al instatnces (translates the generics to concrete values)
    *
    * @param model
    * @param program
    * @return
    */
  def getDomains(model:Model,heap:ExtractedHeap,program:ast.Program) :Seq[DomainEntry] = {
    val domains = program.collect(x=> x match {
      case a:ast.Domain => a
    })
    val concreteDoms = program.collect(x=> x match{//find all definitive type instances
      
     case a:ast.Type=> a match {
       case ast.DomainType(n,map) => Some((n,map))
       
       case _ => None
      } 
      case e:ast.Exp => e match {
        case d:ast.DomainFuncApp => Some((d.domainName,d.typVarMap))//sometimes we use a function without having an actual member of this...
        case _ => None
      }
    }).collect({case Some(x)=>x}).filterNot(x=>containsTypeVar(x._2.values.toSeq)).toSet //make shure we have all the possible mappings without duplicates 
    
    val doms = domains.flatMap(x=>if(x.typVars==Nil) Seq((x,Map.empty[ast.TypeVar,ast.Type])) else concreteDoms.filter(_._1==x.name).map(y=>(x,y._2))) // changing the typevars to the actual ones
    
    doms.map(x=>DomainEntry(x._1.name,
                          try{x._1.typVars.map(x._2)}catch{case _ => {/* printf(s"$x"); */Seq()}},//problem: throws 
                          x._1.functions.map(y=>translateFunction(model,heap,y,x._2))
                          )
            ).toSeq
   
  }
  def containsTypeVar(s:Seq[ast.Type]):Boolean={//helper function
    s.map(x=>x.isInstanceOf[ast.TypeVar]).contains(true)
  }
  //extract all non domain internal functions
  def getFunctions(model:Model,heap:ExtractedHeap,program:ast.Program):Seq[ExtractedFunction]={
    val funcs=program.collect(x=>x match {
      case f:ast.Function => f
    })
    //printf(s"${funcs.map(x=>(x.typ,x.name)).mkString("\n")}")
    funcs.map(x=>translateFunction(model,heap,x,Nil.toMap)).toSeq 
  }

  val emptymap =Map.empty[Seq[ExtractedModelEntry],ExtractedModelEntry]
  def errorfunc(s:String) =  ExtractedFunction("ERROR",Seq(),sorts.Unit,emptymap,OtherEntry("ERROR",s))
  /**
    * extracts the function instances by searching for the most likely match translating the values in the internal rep
    *
    * @param model
    * @param func the function to translate
    * @param genmap map of generic types to concrete types
    * @return
    */
  def translateFunction(model:Model,heap:ExtractedHeap,func:ast.FuncLike,genmap:Map[ast.TypeVar,ast.Type]):ExtractedFunction= {
    val fname =func.name
    val typ :ast.Type = func.typ
    //one might argue it is simpler to do with a Try[] object do it if you have time
      val argtyp :Seq[Sort] = func.formalArgs.map(x=>try {symbolConverter.toSort(x.typ)} catch{ case _ =>x.typ match {
                                                      case x :ast.GenericType =>try{ symbolConverter.toSort(x.substitute(genmap))}catch{ case _ => return errorfunc(fname+"typeError in args")}
                                                      case t:ast.TypeVar => try{symbolConverter.toSort(genmap.apply(t)) }catch{ case _ => return errorfunc(fname+"typeError in args")}
                                                      case _ => return errorfunc("type not resolvable")
                                                        }}
                                                  )
      val resSort :Sort= try {symbolConverter.toSort(typ)}
                              catch{case e:Throwable =>
                                      {
                                        typ match {
                                                      case x :ast.GenericType =>try{ symbolConverter.toSort(x.substitute(genmap))}catch{ case _ => return errorfunc(fname+" typeError in return type")}
                                                      case t:ast.TypeVar => try{symbolConverter.toSort(genmap.apply(t)) }catch{ case _ => return errorfunc(fname+" typeError in return type")}
                                                      case _ => return errorfunc("type not resolvable")
                                                        }
                                      }
                               }
      val smtfunc = func match {
        case t:ast.Function => symbolConverter.toFunction(t).id 
        case t:ast.DomainFunc =>symbolConverter.toFunction(t,argtyp:+resSort).id 
        case t:ast.BackendFunc =>symbolConverter.toFunction(t).id 
      }
      val kek =smtfunc.toString.replace("[","<").replace("]",">").replace(", ","~_") // this is a hack TODO: replace with smt converter when possible
      val entries  = model.entries
      val keys = entries.keys
      //printf(s"$fname: $resSort")
      val modelFuncname = (keys.filter(_.contains(fname+"%limited"))++ (keys.filter(_==fname))++
                          (keys.filter(_==kek))
                           ).head //TODO: make this better
      val simpleRet=(entries.get(modelFuncname)) match {
        case Some(MapEntry(m, els)) => { 
                                        ExtractedFunction(fname,
                                                          argtyp,
                                                          resSort,
                                                          try {m.map(x=>(x._1.zip(argtyp).map(y=>getConstantEntry(y._2,y._1)) ->getConstantEntry(resSort,x._2)))} catch{case t:Throwable=>{emptymap}}, //TODO: this throws NumberFormatException
                                                          getConstantEntry(resSort,els)
                                                          )
                                        }
        case Some(ConstantEntry(t)) => ExtractedFunction(fname,argtyp,resSort,emptymap,getConstantEntry(resSort,ConstantEntry(t)))   
        case Some(ApplicationEntry(n,args)) => ExtractedFunction(fname,argtyp,resSort,emptymap,getConstantEntry(resSort,ApplicationEntry(n,args)))
        case Some(x) => ExtractedFunction(fname,argtyp,resSort,emptymap,getConstantEntry(resSort,x))
        case Some(_) => ExtractedFunction(fname,argtyp,resSort,emptymap,OtherEntry(s"${model.entries.get(fname)}", "not a function"))
        case None    => ExtractedFunction(fname,argtyp,resSort,emptymap,OtherEntry(s"${fname}", "function not found"))
      }
      simpleRet
  }
}

case class Converter(
    model: Model,
    store: Store,
    heap: Iterable[Chunk],
    oldHeaps: State.OldHeaps,
    program:ast.Program
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
  lazy val domains : Seq[DomainEntry] = {Converter.getDomains(model,extractedHeap,program)}
  lazy val non_domain_functions: Seq[ExtractedFunction]= Converter.getFunctions(model,extractedHeap,program)
  def extractVal(x:VarEntry) = Converter.mapLocalVar(model=model,heap=extractedHeap,encountered = Set(),nullRefName = model.entries(Converter.nullRefId).toString,termEval=x,sort=Some(x.sort))
}
/** Entry for user defined domains 
 *  CAREFUL: the types are included in the domain name and do not correspond directly to the name of a DomainEntry
 *  rather they correspond to the valueName in the DomainEntry 
 **/
case class DomainValueEntry(domain:String,id:String) extends ExtractedModelEntry{
  def asValueEntry: ValueEntry = ConstantEntry(toString)
  override def toString: String = s"${domain}_$id"
  def getDomainName :String =domain.takeWhile(_!='[')
}
/** same as DomainValueEntry but with some inforamtion about functions defined on this domain an their coresponding result when using original as input for the function */
case class ExtendedDomainValueEntry(original:DomainValueEntry,info:Map[ExtractedFunction,ExtractedModelEntry]) extends ExtractedModelEntry{
	def asValueEntry =original.asValueEntry
	override def toString = original.toString ++" where " ++ //info.map(_._1.toString).mkString++
                           info.map(x=>x._1.fname ++ " = " ++ x._2.toString.flatMap(y=> y match {
                                                            case '\n' => "\n\t"
                                                            case _ => y+:"" })).mkString("{\n\t",";\n\t","\n\t}")
}
/**
  * Domain entry for specific types, can also be generic
  *  does not contain axioms 
  *
  * @param name Domain name in viper
  * @param types type instances or generic types
  * @param functions functions defined within the domain not includeing functions that use this domain
  */
case class DomainEntry( name:String,
                        types:Seq[ast.Type],
                        functions:Seq[ExtractedFunction]
                      ){
   override def toString :String ={
     s"domain $valueName{\n ${functions.map(_.toString()).mkString("\n")}\n}"
   }
   val valueName :String =s"$name${if(types.isEmpty)""else types.map(printTypes(_)).mkString("[",", ","]")}" // TODO: find out if this is how they are used in the id
   def printTypes(t:ast.Type):String ={
       t match {
         case ast.TypeVar(x) => x
         case _ => t.toString()
       }
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
case class ExtractedFunction( fname:String,
                              argtypes:Seq[Sort],
                              returnType:Sort,
                              options:Map[Seq[ExtractedModelEntry], ExtractedModelEntry],
                              default:ExtractedModelEntry
                            ){
  def apply(args:Seq[ExtractedModelEntry]) : Either[ExtractedFunction,ExtractedModelEntry]= {//TODO: Beautify
    val n = args.length
    val arglength = argtypes.length
    if(n== arglength ) {//full application
      if(typecheck(args,argtypes))
        Right(options.getOrElse(args,default))
      else
        throw new IllegalArgumentException("false types: required "+s"$argtypes"+ " but got: "+ s"$args")
    }else{
      if(n<arglength){
        val (subtypes,rest) = argtypes.splitAt(n)
        if(typecheck(args,subtypes))
          Left(ExtractedFunction(fname+s"_${arglength-n}",
                                  rest,
                                  returnType,
                                  options.filter(x=>x._1.take(n)==args).map(x=>(x._1.drop(n)->x._2)), //map to simpler function
                                  default
                                ))//new function with the first n elements applied
        else throw new IllegalArgumentException("false types for partial application: required "+s"$subtypes"+ " but got: "+ s"$args")
      }else
        throw new IllegalArgumentException(s"to many arguments for function:$fname")
    }
  }
  override def toString: String = {
    if (options.nonEmpty)
      s"$fname${argtypes.mkString("(",",",")")}:$returnType{\n" + options.map(o => "    " + o._1.mkString(" ") + " -> " + o._2).mkString("\n") + "\n    else -> " + default +"\n}"
    else
      s"$fname{\n    " + default +"\n}"
  }
  def typecheck(is:Seq[ExtractedModelEntry],should:Seq[Sort]) :Boolean= {
      is.zip(should).foldLeft(true)((x:(Boolean),y:(ExtractedModelEntry,Sort)) => (x && typecheck(y._1,y._2)))
  }
  def typecheck(is:ExtractedModelEntry,should:Sort):Boolean = {
    is match {
      case LitIntEntry(_) => should == sorts.Int
      case LitBoolEntry(_) => should == sorts.Bool
      case LitPermEntry(_) => should == sorts.Perm
      case RefEntry(_, _) 
      | NullRefEntry(_) 
      | RecursiveRefEntry(_) => should ==sorts.Ref
      case VarEntry(_, sort) => should == sort
      case OtherEntry(_, _) => false
      case SeqEntry(name, values) => should match {case sorts.Seq(e) => if(values.isEmpty) typecheck(values.head,e) else true ; case _ => false}
      case UnprocessedModelEntry(entry) => false
      case DomainValueEntry(domain, id) => should.toString == domain
      case ExtendedDomainValueEntry(original, info) => typecheck(original,should)
    }
  }
}
