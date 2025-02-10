// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.decider

import viper.silicon.decider.SmtlibNameSanitizer
import viper.silicon.interfaces.decider.TermConverter
import viper.silicon.state.terms._
import viper.silicon.state.{Identifier, SimpleIdentifier, SortBasedIdentifier, SuffixedIdentifier}
import viper.silver.components.StatefulComponent
import com.microsoft.z3.{ArithExpr, BoolExpr, Context, DatatypeSort, IntExpr, RealExpr, Expr => Z3Expr, FuncDecl => Z3FuncDecl, Sort => Z3Sort, Symbol => Z3Symbol}

import scala.collection.mutable

class TermToZ3APIConverter
    extends TermConverter[Z3Expr, Z3Sort, Unit]
       with StatefulComponent {

  private var sanitizedNamesCache: mutable.Map[String, String] = _

  private val nameSanitizer = new SmtlibNameSanitizer

  private val smtlibConverter = new TermToSMTLib2Converter()

  var ctx: Context = _
  val macros = mutable.HashMap[String, (Seq[Var], Term)]()

  val sortCache = mutable.HashMap[Sort, Z3Sort]()
  val funcDeclCache = mutable.HashMap[(String, Seq[Sort], Sort), Z3FuncDecl]()
  val smtFuncDeclCache = mutable.HashMap[(String, Seq[Sort]), (Z3FuncDecl, Seq[Z3Expr])]()
  val termCache = mutable.HashMap[Term, Z3Expr]()

  def convert(s: Sort): Z3Sort = convertSort(s)

  def convertId(id: Identifier, sanitizeIdentifier: Boolean = true): String = {
    smtlibConverter.render(id, sanitizeIdentifier)
  }

  def getSnapSort = {
    if (snapSort == null) {
      /*
      (declare-datatypes (($Snap 0)) ((
      ($Snap.unit)
      ($Snap.combine ($Snap.first $Snap) ($Snap.second $Snap)))))
     */
      val unit = ctx.mkConstructor("$Snap.unit", "is_$Snap.unit", null, null, null)

      val sortArray: Array[Z3Sort] = Array(null, null)
      val combine = ctx.mkConstructor("$Snap.combine", "is_$Snap.combine", Array("$Snap.first", "$Snap.second"), sortArray, Array(0, 0))
      snapSort = ctx.mkDatatypeSort("$Snap", Array(unit, combine))
      unitConstructor = unit.ConstructorDecl()
      combineConstructor = combine.ConstructorDecl()
      val accessors = combine.getAccessorDecls
      firstFunc = accessors(0)
      secondFunc = accessors(1)
    }
    snapSort
  }
  def getUnitConstructor = {
    if (unitConstructor == null)
      getSnapSort
    unitConstructor
  }

  def getCombineConstructor = {
    if (combineConstructor == null)
      getSnapSort
    combineConstructor
  }

  def getFirstFunc = {
    if (firstFunc == null)
      getSnapSort
    firstFunc
  }

  def getSecondFunc = {
    if (secondFunc == null)
      getSnapSort
    secondFunc
  }

  var snapSort : DatatypeSort = _
  var unitConstructor : Z3FuncDecl = _
  var combineConstructor: Z3FuncDecl = _
  var firstFunc: Z3FuncDecl = _
  var secondFunc: Z3FuncDecl = _

  def convertSort(s: Sort): Z3Sort = {
    val existingEntry = sortCache.get(s)
    if (existingEntry.isDefined)
      return existingEntry.get
    val res = s match {
      case sorts.Int => ctx.mkIntSort()
      case sorts.Bool => ctx.mkBoolSort()
      case sorts.Perm => ctx.mkRealSort()
      case sorts.Snap => getSnapSort
      case sorts.Ref => ctx.mkUninterpretedSort("$Ref")
      case sorts.Map(keySort, valueSort) => ctx.mkUninterpretedSort("Map<" + convertSortName(keySort) + "~_" + convertSortName(valueSort) + ">")
      case sorts.Seq(elementSort) => {
        val res = ctx.mkUninterpretedSort("Seq<" + convertSortName(elementSort) + ">")
        res
      }
      case sorts.Set(elementSort) => ctx.mkUninterpretedSort("Set<" + convertSortName(elementSort) + ">")
      case sorts.Multiset(elementSort) => ctx.mkUninterpretedSort("Multiset<" + convertSortName(elementSort) + ">")
      case sorts.UserSort(id) => ctx.mkUninterpretedSort(convertId(id))
      case sorts.SMTSort(id) => {
        // workaround: since we cannot create a built-in sort from its name, we let Z3 parse
        // a string that uses the sort, take the AST, and get the func decl from there, so that we can
        // programmatically create a func app.
        val workaround = ctx.parseSMTLIB2String(s"(declare-const workaround ${id}) (assert (= workaround workaround))", null, null, null, null)
        val res = workaround(0).getArgs()(0).getSort
        res
      }

      case sorts.Unit =>
        /* Should never occur
         */
        ???

      case sorts.FieldValueFunction(_, fieldName) => {
        ctx.mkUninterpretedSort("$FVF<" + fieldName + ">")
      }
      case sorts.PredicateSnapFunction(_, predName) => ctx.mkUninterpretedSort("$PSF<" + predName + ">")

      case sorts.FieldPermFunction() => ctx.mkUninterpretedSort("$FPM") // text("$FPM")
      case sorts.PredicatePermFunction() => ctx.mkUninterpretedSort("$PPM") // text("$PPM")
      case sorts.MagicWandSnapFunction => ctx.mkUninterpretedSort("$MWSF")
    }
    sortCache.update(s, res)
    res
  }

  def convertSortSymbol(s: Sort): Option[Z3Symbol] = {
    s match {
      case sorts.Int => None
      case sorts.Bool => None
      case sorts.Perm => None
      case sorts.Snap => Some(ctx.mkSymbol("$Snap"))
      case sorts.Ref => Some(ctx.mkSymbol("$Ref"))
      case sorts.Map(keySort, valueSort) => Some(ctx.mkSymbol("Map<" + convertSortName(keySort) + "~_" + convertSortName(valueSort) + ">"))
      case sorts.Seq(elementSort) => Some(ctx.mkSymbol("Seq<" + convertSortName(elementSort) + ">"))
      case sorts.Set(elementSort) => Some(ctx.mkSymbol("Set<" + convertSortName(elementSort) + ">"))
      case sorts.Multiset(elementSort) => Some(ctx.mkSymbol("Multiset<" + convertSortName(elementSort) + ">"))
      case sorts.UserSort(id) => Some(ctx.mkSymbol(convertId(id)))
      case sorts.SMTSort(_) => {
        ???
      }

      case sorts.Unit =>
        /* Should never occur
         */
        ???

      case sorts.FieldValueFunction(_, fieldName) => Some(ctx.mkSymbol("$FVF<" + fieldName + ">")) //
      case sorts.PredicateSnapFunction(_, predName) => Some(ctx.mkSymbol("$PSF<" + predName + ">"))

      case sorts.FieldPermFunction() => Some(ctx.mkSymbol("$FPM")) // text("$FPM")
      case sorts.PredicatePermFunction() => Some(ctx.mkSymbol("$PPM")) // text("$PPM")
      case sorts.MagicWandSnapFunction => Some(ctx.mkSymbol("$MWSF"))
    }
  }

  def convertSortName(sort: Sort): String = {
    smtlibConverter.convertSanitized(sort)
  }

  def convert(fd: FunctionDecl): Z3FuncDecl = {
    ctx.mkFuncDecl(convertId(fd.func.id), fd.func.argSorts.filter(s => s != viper.silicon.state.terms.sorts.Unit).map(convertSort(_)).toArray, convertSort(fd.func.resultSort))
  }

  def convertFuncSymbol(fd: FunctionDecl): Z3Symbol = {
    ctx.mkSymbol(convertId(fd.func.id))
  }
  
  def convert(md: MacroDecl): (Z3FuncDecl, BoolExpr) = {
    val func = ctx.mkFuncDecl(convertId(md.id), md.args.map(a => convertSort(a.sort)).toArray, convertSort(md.body.sort))
    val app = ctx.mkApp(func, md.args.map(convert(_)).toArray : _*)
    val patterns = Array(ctx.mkPattern(app))
    val quant = ctx.mkForall(md.args.map(convert(_)).toArray, ctx.mkEq(convertTerm(md.body), app), 1, patterns, null, ctx.mkSymbol(md.id.name), null)
    (func, quant)
  }

  def convert(swd: SortWrapperDecl): Z3FuncDecl = {
    val id = swd.id
    val fct = FunctionDecl(Fun(id, swd.from, swd.to))
    convert(fct)
  }

  def convertSortWrapperSymbol(swd: SortWrapperDecl) = {
    val id = swd.id
    val fct = FunctionDecl(Fun(id, swd.from, swd.to))
    convertFuncSymbol(fct)
  }

  def convert(d: Decl): Unit = {
    // not used
    ???
  }

  def convert(t: Term): Z3Expr = {
    convertTerm(t)
  }


  def convertTerm(term: Term): Z3Expr = {
    val cached = termCache.get(term)
    if (cached.isDefined)
      return cached.get
    val res = term match {
      case l: Literal => {
        l match {
          case IntLiteral(n) => {
            if (n >= 0)
              ctx.mkInt(n.toString())
            else
              ctx.mkUnaryMinus(ctx.mkInt((-n).toString()))
          }
          case True => ctx.mkTrue()
          case False => ctx.mkFalse()
          case Null => ctx.mkConst("$Ref.null", ctx.mkUninterpretedSort("$Ref"))
          case Unit => ctx.mkConst(getUnitConstructor)
          case _: SeqNil => createApp("Seq_empty", Seq(), l.sort)
          case _: EmptySet => createApp("Set_empty", Seq(), l.sort)
          case _: EmptyMultiset => createApp("Multiset_empty", Seq(), l.sort)
          case _: EmptyMap => createApp("Map_empty", Seq(), l.sort)
        }
      }

      case Ite(t0, t1, t2) =>
        ctx.mkITE(convertTerm(t0).asInstanceOf[BoolExpr], convertTerm(t1), convertTerm(t2))

      case x: Var =>
        ctx.mkConst(convertId(x.id), convertSort(x.sort))

      case fapp: Application[_] =>
        fapp.applicable match {
          case _: SMTFun => createSMTApp(convertId(fapp.applicable.id, false), fapp.args)
          case _ => {
            if (macros.contains(fapp.applicable.id.name)) {
              val (vars, body) = macros(fapp.applicable.id.name)
              if (vars.length != fapp.args.length)
                sys.error("macro usage doesn't match")
              val substituted = body.replace(vars, fapp.args)
              val res = convert(substituted)
              res
            } else {
              createApp(convertId(fapp.applicable.id), fapp.args, fapp.sort)
            }
          }
        }


      /* Handle quantifiers that have at most one trigger set */
      case Quantification(quant, vars, body, triggers, name, _, weight) => {
        if (vars.isEmpty) {
          convertTerm(body)
        } else{
          val qvarExprs = vars.map(v => convert(v)).toArray
          val nonEmptyTriggers = triggers.filter(_.p.nonEmpty)
          val patterns = if (nonEmptyTriggers.nonEmpty) {
              // ME: Maybe we should simplify trigger terms here? There is some evidence that Z3 does this
              // automatically when used via stdio, and it sometimes makes triggers valid that would otherwise be
              // rejected. On the other hand, it's not at all obvious that simplification does not change the shape
              // of a trigger term, which would not be what we want.
              nonEmptyTriggers.map(t => ctx.mkPattern(t.p.map(trm => convertTerm(trm)): _*)).toArray
          } else null
          val weightValue = weight.getOrElse(1)
          if (quant == Forall) {
            ctx.mkForall(qvarExprs, convertTerm(body), weightValue, patterns, null, ctx.mkSymbol(name), null)
          } else {
            ctx.mkExists(qvarExprs, convertTerm(body), weightValue, patterns, null, ctx.mkSymbol(name), null)
          }
        }
      }

      /* Booleans */

      case uop: Not => ctx.mkNot(convertTerm(uop.p).asInstanceOf[BoolExpr])
      case And(ts) => ctx.mkAnd(ts.map(convertTerm(_).asInstanceOf[BoolExpr]): _*)
      case Or(ts) => ctx.mkOr(ts.map(convertTerm(_).asInstanceOf[BoolExpr]): _*)
      case bop: Implies => ctx.mkImplies(convertTerm(bop.p0).asInstanceOf[BoolExpr], convertTerm(bop.p1).asInstanceOf[BoolExpr])
      case bop: Iff =>
      {
        val t0 = convertTerm(bop.p0).asInstanceOf[BoolExpr]
        val t1 = convertTerm(bop.p1).asInstanceOf[BoolExpr]
        val implication1 = ctx.mkImplies(t0, t1)
        val implication2 = ctx.mkImplies(t1, t0)
        ctx.mkAnd(implication1, implication2)
      }
      case bop: BuiltinEquals => ctx.mkEq(convertTerm(bop.p0), convertTerm(bop.p1))

      case bop: CustomEquals => bop.p0.sort match {
        case _: sorts.Seq => createApp("Seq_equal", Seq(bop.p0, bop.p1), bop.sort)
        case _: sorts.Set => createApp("Set_equal", Seq(bop.p0, bop.p1), bop.sort)
        case _: sorts.Multiset => createApp("Multiset_equal", Seq(bop.p0, bop.p1), bop.sort)
        case _: sorts.Map => createApp("Map_equal", Seq(bop.p0, bop.p1), bop.sort)
        case sort => sys.error(s"Don't know how to translate equality between symbols $sort-typed terms")
      }

      /* Arithmetic */

      case bop: Minus => ctx.mkSub(convertTerm(bop.p0).asInstanceOf[ArithExpr], convertTerm(bop.p1).asInstanceOf[ArithExpr])
      case bop: Plus => ctx.mkAdd(convertTerm(bop.p0).asInstanceOf[ArithExpr], convertTerm(bop.p1).asInstanceOf[ArithExpr])
      case bop: Times => ctx.mkMul(convertTerm(bop.p0).asInstanceOf[ArithExpr], convertTerm(bop.p1).asInstanceOf[ArithExpr])
      case bop: Div => ctx.mkDiv(convertTerm(bop.p0).asInstanceOf[ArithExpr], convertTerm(bop.p1).asInstanceOf[ArithExpr])
      case bop: Mod => ctx.mkMod(convertTerm(bop.p0).asInstanceOf[IntExpr], convertTerm(bop.p1).asInstanceOf[IntExpr])

      /* Arithmetic comparisons */

      case bop: Less => ctx.mkLt(convertTerm(bop.p0).asInstanceOf[ArithExpr], convertTerm(bop.p1).asInstanceOf[ArithExpr])
      case bop: AtMost => ctx.mkLe(convertTerm(bop.p0).asInstanceOf[ArithExpr], convertTerm(bop.p1).asInstanceOf[ArithExpr])
      case bop: AtLeast => ctx.mkGe(convertTerm(bop.p0).asInstanceOf[ArithExpr], convertTerm(bop.p1).asInstanceOf[ArithExpr])
      case bop: Greater => ctx.mkGt(convertTerm(bop.p0).asInstanceOf[ArithExpr], convertTerm(bop.p1).asInstanceOf[ArithExpr])

      /* Permissions */


      case FullPerm => ctx.mkReal(1)
      case NoPerm => ctx.mkReal(0)
      case FractionPermLiteral(r) => ctx.mkDiv(convertToReal(IntLiteral(r.numerator)), convertToReal(IntLiteral(r.denominator)))
      case FractionPerm(n, d) => ctx.mkDiv(convertToReal(n), convertToReal(d))
      case PermLess(t0, t1) => ctx.mkLt(convertTerm(t0).asInstanceOf[ArithExpr], convertTerm(t1).asInstanceOf[ArithExpr])
      case PermAtMost(t0, t1) => ctx.mkLe(convertTerm(t0).asInstanceOf[ArithExpr], convertTerm(t1).asInstanceOf[ArithExpr])
      case PermPlus(t0, t1) => ctx.mkAdd(convertTerm(t0).asInstanceOf[ArithExpr], convertTerm(t1).asInstanceOf[ArithExpr])
      case PermMinus(t0, t1) => ctx.mkSub(convertTerm(t0).asInstanceOf[ArithExpr], convertTerm(t1).asInstanceOf[ArithExpr])
      case PermTimes(t0, t1) => ctx.mkMul(convertTerm(t0).asInstanceOf[ArithExpr], convertTerm(t1).asInstanceOf[ArithExpr])
      case IntPermTimes(t0, t1) => ctx.mkMul(convertTerm(t0).asInstanceOf[ArithExpr], convertTerm(t1).asInstanceOf[ArithExpr])
      case PermIntDiv(t0, t1) => ctx.mkDiv(convertToReal(t0), convertToReal(t1))
      case PermPermDiv(t0, t1) => ctx.mkDiv(convertToReal(t0), convertToReal(t1))
      case PermMin(t0, t1) => {
        /*
        (define-fun $Perm.min ((p1 $Perm) (p2 $Perm)) Real
    (ite (<= p1 p2) p1 p2))
         */
        val e0 = convert(t0).asInstanceOf[ArithExpr]
        val e1 = convert(t1).asInstanceOf[ArithExpr]
        ctx.mkITE(ctx.mkLe(e0, e1), e0, e1)
      }
      case IsValidPermVal(v) => {
        /*
        (define-fun $Perm.isValidVar ((p $Perm)) Bool
	        (<= $Perm.No p))
         */
        ctx.mkLe(ctx.mkReal(0), convert(v).asInstanceOf[ArithExpr])
      }
      case IsReadPermVar(v) => {
        /*
        (define-fun $Perm.isReadVar ((p $Perm)) Bool
         (and ($Perm.isValidVar p)
         (not (= p $Perm.No))))
         */
        ctx.mkLt(ctx.mkReal(0), convert(v).asInstanceOf[ArithExpr]) // simplified
        //ctx.mkAnd(ctx.mkLe(ctx.mkReal(0), convert(v).asInstanceOf[ArithExpr]),
        //  ctx.mkNot(ctx.mkEq(convert(v).asInstanceOf[ArithExpr], ctx.mkReal(0))))
      }

      /* Sequences */

      case SeqRanged(t0, t1) => createApp("Seq_range", Seq(t0, t1), term.sort)
      case SeqSingleton(t0) => createApp("Seq_singleton", Seq(t0), term.sort)
      case bop: SeqAppend => createApp("Seq_append", Seq(bop.p0, bop.p1), term.sort)
      case uop: SeqLength => createApp("Seq_length", Seq(uop.p), term.sort)
      case bop: SeqAt => createApp("Seq_index", Seq(bop.p0, bop.p1), term.sort)
      case bop: SeqTake => createApp("Seq_take", Seq(bop.p0, bop.p1), term.sort)
      case bop: SeqDrop => createApp("Seq_drop", Seq(bop.p0, bop.p1), term.sort)
      case bop: SeqIn => createApp("Seq_contains", Seq(bop.p0, bop.p1), term.sort)
      case bop: SeqInTrigger => createApp("Seq_contains_trigger", Seq(bop.p0, bop.p1), term.sort)
      case SeqUpdate(t0, t1, t2) => createApp("Seq_update", Seq(t0, t1, t2), term.sort)

      /* Sets */

      case uop: SingletonSet => createApp("Set_singleton", Seq(uop.p), uop.sort)
      case bop: SetAdd => createApp("Set_unionone", Seq(bop.p0, bop.p1), bop.sort)
      case uop: SetCardinality => createApp("Set_card", Seq(uop.p), uop.sort)
      case bop: SetDifference => createApp("Set_difference", Seq(bop.p0, bop.p1), bop.sort)
      case bop: SetIntersection => createApp("Set_intersection", Seq(bop.p0, bop.p1), bop.sort)
      case bop: SetUnion => createApp("Set_union", Seq(bop.p0, bop.p1), bop.sort)
      case bop: SetIn => createApp("Set_in", Seq(bop.p0, bop.p1), bop.sort)
      case bop: SetSubset => createApp("Set_subset", Seq(bop.p0, bop.p1), bop.sort)
      case bop: SetDisjoint => createApp("Set_disjoint", Seq(bop.p0, bop.p1), bop.sort)

      /* Multisets */

      case uop: SingletonMultiset => createApp("Multiset_singleton", Seq(uop.p), uop.sort)
      case bop: MultisetAdd => createApp("Multiset_unionone", Seq(bop.p0, bop.p1), bop.sort)
      case uop: MultisetCardinality => createApp("Multiset_card", Seq(uop.p), uop.sort)
      case bop: MultisetDifference => createApp("Multiset_difference", Seq(bop.p0, bop.p1), bop.sort)
      case bop: MultisetIntersection => createApp("Multiset_intersection", Seq(bop.p0, bop.p1), bop.sort)
      case bop: MultisetUnion => createApp("Multiset_union", Seq(bop.p0, bop.p1), bop.sort)
      case bop: MultisetSubset => createApp("Multiset_subset", Seq(bop.p0, bop.p1), bop.sort)
      case bop: MultisetCount => createApp("Multiset_count", Seq(bop.p0, bop.p1), bop.sort)

      /* Maps */

      case m: MapCardinality => createApp("Map_card", Seq(m.p), m.sort)
      case m: MapDomain => createApp("Map_domain", Seq(m.p), m.sort)
      case m: MapRange => createApp("Map_values", Seq(m.p), m.sort)
      case m: MapLookup => createApp("Map_apply", Seq(m.p0, m.p1), m.sort)
      case m: MapUpdate => createApp("Map_update", Seq(m.base, m.key, m.value), m.sort)

      /* Quantified Permissions */

      case Domain(id, fvf) => createApp("$FVF.domain_" + id, Seq(fvf), term.sort)

      case Lookup(field, fvf, at) =>
        createApp("$FVF.lookup_" + field, Seq(fvf, at), term.sort)

      case FieldTrigger(field, fvf, at) => createApp("$FVF.loc_" + field, (fvf.sort match {
        case sorts.FieldValueFunction(_, _) => Seq(Lookup(field, fvf, at), at)
        case _ => Seq(fvf, at)
      }), term.sort)

      case PermLookup(field, pm, at) => createApp("$FVF.perm_" + field, Seq(pm, at), term.sort)

      case PredicateDomain(id, psf) => createApp("$PSF.domain_" + id, Seq(psf), term.sort)

      case PredicateLookup(id, psf, args) =>
        val snap: Term = toSnapTree(args)
        createApp("$PSF.lookup_" + id, Seq(psf, snap), term.sort)

      case PredicateTrigger(id, psf, args) =>
        val snap: Term = toSnapTree(args)
        createApp("$PSF.loc_" + id, Seq(PredicateLookup(id, psf, args), snap), term.sort)

      case PredicatePermLookup(predname, pm, args) =>
        val snap: Term = toSnapTree(args)
        createApp("$PSF.perm_" + predname, Seq(pm, snap), term.sort)

      /* Other terms */

      case First(t) => ctx.mkApp(firstFunc, convertTerm(t))
      case Second(t) => ctx.mkApp(secondFunc, convertTerm(t))

      case bop: Combine =>
        ctx.mkApp(combineConstructor, convertTerm(bop.p0), convertTerm(bop.p1))

      case SortWrapper(t, to) =>
        createApp(convertId(SortWrapperId(t.sort, to)), Seq(t), to)

      case Distinct(symbols) =>
        ctx.mkDistinct(symbols.map(s => ctx.mkConst(convertId(s.id), convertSort(s.resultSort))).toSeq: _*)

      case Let(bindings, body) =>
        convert(body.replace(bindings))

      case MWSFLookup(mwsf, snap) => createApp("MWSF_apply", Seq(mwsf, snap), sorts.Snap)

      case _: MagicWandChunkTerm
         | _: Quantification =>
        sys.error(s"Unexpected term $term cannot be translated to SMTLib code")
    }
    termCache.put(term, res)
    res
  }

  @inline
  protected def createApp(functionName: String, args: Seq[Term], outSort: Sort): Z3Expr = {
    ctx.mkApp(getFuncDecl(functionName, outSort, args.map(_.sort)), args.map(convertTerm(_)): _*)
  }

  def getFuncDecl(name: String, resSort: Sort, argSorts: Seq[Sort]): Z3FuncDecl = {
    val existingEntry = funcDeclCache.get((name, argSorts, resSort))
    if (existingEntry.isDefined)
      return existingEntry.get
    val res = ctx.mkFuncDecl(name, argSorts.map(a => convertSort(a)).toArray, convertSort(resSort))
    funcDeclCache.update((name, argSorts, resSort), res)
    res
  }


  @inline
  protected def createSMTApp(functionName: String, args: Seq[Term]): Z3Expr = {
    // workaround: since we cannot create a function application with just the name, we let Z3 parse
    // a string that uses the function, take the AST, and get the func decl from there, so that we can
    // programmatically create a func app.

    val cacheKey = (functionName, args.map(_.sort))
    val (decl, additionalArgs: Seq[Z3Expr]) = if (smtFuncDeclCache.contains(cacheKey)) {
      smtFuncDeclCache(cacheKey)
    } else {
      val declPreamble = "(define-sort $Perm () Real) " // ME: Re-declare the Perm sort.
      // ME: The parsing happens in a fresh context that doesn't know any of our current declarations.
      // In principle, it might be necessary to re-declare all sorts we're using anywhere. However, I don't see how there
      // could be any Z3 internal functions that exist for those custom sorts. For the Real (i.e., Perm) sort, however,
      // such functions exist. So we re-declare *only* this sort.
      val decls = declPreamble + args.zipWithIndex.map { case (a, i) => s"(declare-const workaround${i} ${smtlibConverter.convert(a.sort)})" }.mkString(" ")
      val funcAppString = if (args.nonEmpty)
        s"(${functionName} ${(0 until args.length).map(i => "workaround" + i).mkString(" ")})"
      else
        functionName
      val assertion = decls + s" (assert (= ${funcAppString} ${funcAppString}))"
      val workaround = ctx.parseSMTLIB2String(assertion, null, null, null, null)
      val app = workaround(0).getArgs()(0)
      val decl = app.getFuncDecl
      val additionalArgs = if (decl.getArity > args.length) {
        // the function name we got wasn't just a function name but also contained a first argument.
        // this happens with float operations where functionName contains a rounding mode.
        app.getArgs.toSeq.slice(0, decl.getArity - args.length)
      } else {
        Seq()
      }
      smtFuncDeclCache.put(cacheKey, (decl, additionalArgs))
      (decl, additionalArgs)
    }

    val actualArgs = additionalArgs ++ args.map(convertTerm(_))
    ctx.mkApp(decl, actualArgs.toArray : _*)
  }


  protected def convertToReal(t: Term): RealExpr =
    if (t.sort == sorts.Int)
      ctx.mkInt2Real(convertTerm(t).asInstanceOf[IntExpr])
    else
      convertTerm(t).asInstanceOf[RealExpr]

  protected def render(id: Identifier, sanitizeIdentifier: Boolean = true): String = {
    val repr: String = id match {
      case SimpleIdentifier(name) => name
      case SuffixedIdentifier(prefix, separator, suffix) => s"${render(prefix, false)}$separator$suffix"
      case SortBasedIdentifier(template, sorts) => template.format(sorts.map(convert): _*)
    }

    if (sanitizeIdentifier) sanitize(repr)
    else repr
  }

  private def sanitize(str: String): String = {
    val sanitizedName = sanitizedNamesCache.getOrElseUpdate(str, nameSanitizer.sanitize(str))

    sanitizedName
  }

  def start(): Unit = {
    sanitizedNamesCache = mutable.Map.empty
    smtlibConverter.start()
  }

  def reset(): Unit = {
    ctx = null
    smtlibConverter.reset()
    sanitizedNamesCache.clear()
    macros.clear()
    funcDeclCache.clear()
    smtFuncDeclCache.clear()
    sortCache.clear()
    termCache.clear()
    unitConstructor = null
    combineConstructor = null
    firstFunc = null
    secondFunc = null
    snapSort = null
  }

  def stop(): Unit = {
    if (sanitizedNamesCache != null) sanitizedNamesCache.clear()
  }

  override def convertSanitized(s: Sort): Z3Sort = convertSort(s)
}
