// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.decider

import scala.collection.mutable
import viper.silver.ast.pretty.FastPrettyPrinterBase
import viper.silver.components.StatefulComponent
import viper.silicon.interfaces.decider.TermConverter
import viper.silicon.state.{Identifier, SimpleIdentifier, SortBasedIdentifier, SuffixedIdentifier}
import viper.silicon.state.terms._

class TermToSMTLib2Converter 
    extends FastPrettyPrinterBase
       with TermConverter[String, String, String]
       with StatefulComponent {

  override val defaultIndent = 2
  override val defaultWidth = 80

  lazy val uninitialized: Cont = value("<not initialized>")

  private var sanitizedNamesCache: mutable.Map[String, String] = _

  private val nameSanitizer = new SmtlibNameSanitizer

  def convert(s: Sort): String = {
    super.pretty(defaultWidth, render(s))
  }

  def convertSanitized(s: Sort): String = {
    super.pretty(defaultWidth, doRender(s, true))
  }

  protected def render(sort: Sort) = doRender(sort, false)

  protected def doRender(sort: Sort, alwaysSanitize: Boolean = false): Cont = sort match {
    case sorts.Int => "Int"
    case sorts.Bool => "Bool"
    case sorts.Perm => "$Perm"
    case sorts.Snap => "$Snap"
    case sorts.Ref => "$Ref"
    case sorts.Map(keySort, valueSort) => text("Map") <> "<" <> doRender(keySort, true) <> "~_" <> doRender(valueSort, true) <> ">"
    case sorts.Seq(elementSort) => text("Seq<") <> doRender(elementSort, true) <> ">"
    case sorts.Set(elementSort) => text("Set<") <> doRender(elementSort, true) <> ">"
    case sorts.Multiset(elementSort) => text("Multiset<") <> doRender(elementSort, true) <> ">"
    case sorts.UserSort(id) => render(id)
    case sorts.SMTSort(id) => if (alwaysSanitize) render(id) else id.name

    case sorts.Unit =>
      /* Sort Unit corresponds to Scala's Unit type and is used, e.g., as the
       * domain sort of nullary functions.
       */
      ""

    case sorts.FieldValueFunction(_, fieldName) => text("$FVF<") <> text(fieldName) <> ">"
    case sorts.PredicateSnapFunction(_, predName) => text("$PSF<") <> text(predName) <> ">"

    case sorts.FieldPermFunction() => text("$FPM")
    case sorts.PredicatePermFunction() => text("$PPM")

    case sorts.MagicWandSnapFunction => text("$MWSF")
  }

  def convert(d: Decl): String = {
    super.pretty(defaultWidth, render(d))
  }

  protected def render(decl: Decl): Cont = decl match {
    case SortDecl(sort: Sort) =>
      parens(text("declare-sort") <+> render(sort) <+> text("0"))

    case FunctionDecl(fun: Function) =>
      val idDoc = render(fun.id)
      val argSortsDoc = fun.argSorts.map(render)
      val resultSortDoc = render(fun.resultSort)

      if (argSortsDoc.isEmpty)
        parens(text("declare-const") <+> idDoc <+> resultSortDoc)
      else
        parens(text("declare-fun") <+> idDoc <+> parens(ssep(argSortsDoc.to(collection.immutable.Seq), space)) <+> resultSortDoc)

    case swd @ SortWrapperDecl(from, to) =>
//      val id = Identifier(sortWrapperName(from, to))
      val id = swd.id
      val fct = FunctionDecl(Fun(id, from, to))

      render(fct)

    case MacroDecl(id, args, body) =>
      val idDoc = render(id)
      val argDocs = (args map (v => parens(text(render(v.id)) <+> render(v.sort)))).to(collection.immutable.Seq)
      val bodySortDoc = render(body.sort)
      val bodyDoc = render(body)

      parens(text("define-fun") <+> idDoc <+> parens(ssep(argDocs, space)) <+> bodySortDoc <> nest(defaultIndent, line <> bodyDoc))
  }

  def convert(t: Term): String = {
    super.pretty(defaultWidth, render(t))
  }

  protected def render(term: Term): Cont = term match {
    case lit: Literal => render(lit)

    case Ite(t0, t1, t2) =>
      renderNAryOp("ite", t0, t1, t2)

    case x: Var =>
      render(x.id)

    case fapp: Application[_] =>
      fapp.applicable match {
        case _: SMTFun => renderSMTApp(fapp.applicable.id.name, fapp.args, fapp.sort)
        case _ => renderApp(fapp.applicable.id.name, fapp.args, fapp.sort)
      }


    /* Handle quantifiers that have at most one trigger set */
    case Quantification(quant, vars, body, triggers, name, _, weight) =>
      val docBody = render(body)

      if (vars.nonEmpty) {
        val docVars = ssep((vars map (v => parens(text(render(v.id)) <+> render(v.sort)))).to(collection.immutable.Seq), space)
        val docQuant = render(quant)

        // Render only triggers with non-empty terms since cvc5 breaks on
        // empty patterns (i.e. :pattern ()).
        val renderedTriggerTerms = triggers.collect {
            case trigger if trigger.p.nonEmpty => ssep((trigger.p map render).to(collection.immutable.Seq), space)
          }

        val docTriggers =
          if (renderedTriggerTerms.isEmpty)
            nil
          else
            ssep(renderedTriggerTerms.map(d => text(":pattern") <+> parens(d)).to(collection.immutable.Seq), line)

        val docQid: Cont =
          if (name.isEmpty) nil
          else s":qid |$name|"

        val docWeight = weight match {
          case Some(value) => line <> text(":weight") <+> value.toString
          case None => nil
        }

        // Omit annotation for empty name and triggers since cvc5 fails
        // for annotations containing zero attributes (Z3 simply ignores it).
        if (name.isEmpty && triggers.isEmpty)
          parens(docQuant <+> parens(docVars) <+> nest(defaultIndent, line <> docBody <> docWeight))
        else
          parens(docQuant <+> parens(docVars) <+> parens(text("!") <> nest(defaultIndent, line <> docBody <> line <> docTriggers <> line <> docQid <> docWeight)))
      } else {
        // TODO: This seems like a hack.
        //       It would be better to avoid creating quantifications with no variables in the first place.
        text(s"; WARNING: Got invalid quantifier: $term") <@> docBody
      }

    /* Booleans */

    case uop: Not => renderUnaryOp("not", uop)
    case And(ts) => renderNAryOp("and", ts: _*)
    case Or(ts) => renderNAryOp("or", ts: _*)
    case bop: Implies => renderBinaryOp("=>", bop)
    case bop: Iff =>  {
        val implication1 = Implies(bop.p0, bop.p1)
        val implication2 = Implies(bop.p1, bop.p0)
        val iff = And(Seq(implication1, implication2))
        render(iff)
    }
    case bop: BuiltinEquals => renderBinaryOp("=", bop)

    case bop: CustomEquals => bop.p0.sort match {
      case _: sorts.Seq => renderBinaryOp("Seq_equal", bop)
      case _: sorts.Set => renderApp("Set_equal", Seq(bop.p0, bop.p1), bop.sort)
      case _: sorts.Multiset => renderApp("Multiset_equal", Seq(bop.p0, bop.p1), bop.sort)
      case _: sorts.Map => renderApp("Map_equal", Seq(bop.p0, bop.p1), bop.sort)
      case sort => sys.error(s"Don't know how to translate equality between symbols $sort-typed terms")
    }

    /* Arithmetic */

    case bop: Minus => renderBinaryOp("-", bop)
    case bop: Plus => renderBinaryOp("+", bop)
    case bop: Times => renderBinaryOp("*", bop)
    case bop: Div => renderBinaryOp("div", bop)
    case bop: Mod => renderBinaryOp("mod", bop)

    /* Arithmetic comparisons */

    case bop: Less => renderBinaryOp("<", bop)
    case bop: AtMost => renderBinaryOp("<=", bop)
    case bop: AtLeast => renderBinaryOp(">=", bop)
    case bop: Greater => renderBinaryOp(">", bop)

    /* Permissions */

    case FullPerm => "$Perm.Write"
    case NoPerm => "$Perm.No"
    case FractionPermLiteral(r) => renderBinaryOp("/", renderAsReal(IntLiteral(r.numerator)), renderAsReal(IntLiteral(r.denominator)))
    case FractionPerm(n, d) => renderBinaryOp("/", renderAsReal(n), renderAsReal(d))
    case PermLess(t0, t1) => renderBinaryOp("<", render(t0), render(t1))
    case PermAtMost(t0, t1) => renderBinaryOp("<=", render(t0), render(t1))
    case PermPlus(t0, t1) => renderBinaryOp("+", renderAsReal(t0), renderAsReal(t1))
    case PermMinus(t0, t1) => renderBinaryOp("-", renderAsReal(t0), renderAsReal(t1))
    case PermTimes(t0, t1) => renderBinaryOp("*", renderAsReal(t0), renderAsReal(t1))
    case IntPermTimes(t0, t1) => renderBinaryOp("*", renderAsReal(t0), renderAsReal(t1))
    case PermIntDiv(t0, t1) => renderBinaryOp("/", renderAsReal(t0), renderAsReal(t1))
    case PermPermDiv(t0, t1) => renderBinaryOp("/", renderAsReal(t0), renderAsReal(t1))
    case PermMin(t0, t1) => renderBinaryOp("$Perm.min", render(t0), render(t1))
    case IsValidPermVal(v) => parens(text("$Perm.isValidVar") <+> render(v))
    case IsReadPermVar(v) => parens(text("$Perm.isReadVar") <+> render(v))

    /* Sequences */

    case SeqRanged(t0, t1) => renderBinaryOp("Seq_range", render(t0), render(t1))
    case SeqSingleton(t0) => parens(text("Seq_singleton") <+> render(t0))
    case bop: SeqAppend => renderBinaryOp("Seq_append", bop)
    case uop: SeqLength => renderUnaryOp("Seq_length", uop)
    case bop: SeqAt => renderBinaryOp("Seq_index", bop)
    case bop: SeqTake => renderBinaryOp("Seq_take", bop)
    case bop: SeqDrop => renderBinaryOp("Seq_drop", bop)
    case bop: SeqIn => renderBinaryOp("Seq_contains", bop)
    case bop: SeqInTrigger => renderBinaryOp("Seq_contains_trigger", bop)
    case SeqUpdate(t0, t1, t2) => renderNAryOp("Seq_update", t0, t1, t2)

    /* Sets */

    case uop: SingletonSet => renderApp("Set_singleton", Seq(uop.p), uop.sort)
    case bop: SetAdd => renderApp("Set_unionone", Seq(bop.p0, bop.p1), bop.sort)
    case uop: SetCardinality => renderApp("Set_card", Seq(uop.p), uop.sort)
    case bop: SetDifference => renderApp("Set_difference", Seq(bop.p0, bop.p1), bop.sort)
    case bop: SetIntersection => renderApp("Set_intersection", Seq(bop.p0, bop.p1), bop.sort)
    case bop: SetUnion => renderApp("Set_union", Seq(bop.p0, bop.p1), bop.sort)
    case bop: SetIn => renderApp("Set_in", Seq(bop.p0, bop.p1), bop.sort)
    case bop: SetSubset => renderApp("Set_subset", Seq(bop.p0, bop.p1), bop.sort)
    case bop: SetDisjoint => renderApp("Set_disjoint", Seq(bop.p0, bop.p1), bop.sort)

    /* Multisets */

    case uop: SingletonMultiset => renderApp("Multiset_singleton", Seq(uop.p), uop.sort)
    case bop: MultisetAdd => renderApp("Multiset_unionone", Seq(bop.p0, bop.p1), bop.sort)
    case uop: MultisetCardinality => renderApp("Multiset_card", Seq(uop.p), uop.sort)
    case bop: MultisetDifference => renderApp("Multiset_difference", Seq(bop.p0, bop.p1), bop.sort)
    case bop: MultisetIntersection => renderApp("Multiset_intersection", Seq(bop.p0, bop.p1), bop.sort)
    case bop: MultisetUnion => renderApp("Multiset_union", Seq(bop.p0, bop.p1), bop.sort)
    case bop: MultisetSubset => renderApp("Multiset_subset", Seq(bop.p0, bop.p1), bop.sort)
    case bop: MultisetCount => renderApp("Multiset_count", Seq(bop.p0, bop.p1), bop.sort)

    /* Maps */

    case m: MapCardinality => renderApp("Map_card", Seq(m.p), m.sort)
    case m: MapDomain => renderApp("Map_domain", Seq(m.p), m.sort)
    case m: MapRange => renderApp("Map_values", Seq(m.p), m.sort)
    case m: MapLookup => renderApp("Map_apply", Seq(m.p0, m.p1), m.sort)
    case m: MapUpdate => renderApp("Map_update", Seq(m.base, m.key, m.value), m.sort)

    /* Quantified Permissions */

    case Domain(id, fvf) => parens(text("$FVF.domain_") <> id <+> render(fvf))

    case Lookup(field, fvf, at) => //fvf.sort match {
//      case _: sorts.PartialFieldValueFunction =>
      parens(text("$FVF.lookup_") <> field <+> render(fvf) <+> render(at))
//      case _: sorts.TotalFieldValueFunction =>
//        render(Apply(fvf, Seq(at)))
//        parens("$FVF.lookup_" <> field <+> render(fvf) <+> render(at))
//      case _ =>
//        sys.error(s"Unexpected sort '${fvf.sort}' of field value function '$fvf' in lookup term '$term'")
//    }

    case FieldTrigger(field, fvf, at) => parens(text("$FVF.loc_") <> field <+> (fvf.sort match {
      case sorts.FieldValueFunction(_, _) => render(Lookup(field, fvf, at)) <+> render(at)
      case _ => render(fvf) <+> render(at)
    }))

    case PermLookup(field, pm, at) => parens(text("$FVF.perm_") <> field <+> render(pm) <+> render(at))

    case PredicateDomain(id, psf) => parens(text("$PSF.domain_") <> id <+> render(psf))

    case PredicateLookup(id, psf, args) =>
      val snap: Term = toSnapTree(args)

      parens(text("$PSF.lookup_") <> id <+> render(psf) <+> render(snap))

    case PredicateTrigger(id, psf, args) =>
      val snap: Term = toSnapTree(args)

      parens(text("$PSF.loc_") <> id <+> render(PredicateLookup(id, psf, args)) <+> render(snap))

    case PredicatePermLookup(predname, pm, args) =>
      val snap: Term = toSnapTree(args)

      parens(text("$PSF.perm_") <> predname <+> render(pm) <+> render(snap))

    /* Other terms */

    case First(t) => parens(text("$Snap.first") <+> render(t))
    case Second(t) => parens(text("$Snap.second") <+> render(t))

    case bop: Combine =>
      renderBinaryOp("$Snap.combine", bop)

    case SortWrapper(t, to) =>
      parens(text(render(SortWrapperId(t.sort, to))) <+> render(t))

    case Distinct(symbols) =>
      parens(text("distinct") <+> ssep((symbols.toSeq map (s => render(s.id): Cont)).to(collection.immutable.Seq), space))

    case Let(bindings, body) =>
      val docBindings = ssep((bindings.toSeq map (p => parens(render(p._1) <+> render(p._2)))).to(collection.immutable.Seq), space)
      parens(text("let") <+> parens(docBindings) <+> render(body))

    case MagicWandSnapshot(mwsf) => render(mwsf)
    case MWSFLookup(mwsf, snap) => renderApp("MWSF_apply", Seq(mwsf, snap), sorts.Snap)

    case _: MagicWandChunkTerm
       | _: Quantification =>
      sys.error(s"Unexpected term $term cannot be translated to SMTLib code")
  }

  @inline
  protected def renderUnaryOp(op: String, t: UnaryOp[Term]): Cont =
    parens(text(op) <> nest(defaultIndent, group(line <> render(t.p))))

  @inline
  protected def renderUnaryOp(op: String, doc: Cont): Cont =
    parens(text(op) <> nest(defaultIndent, group(line <> doc)))

  @inline
  protected def renderBinaryOp(op: String, t: BinaryOp[Term]): Cont =
    parens(text(op) <> nest(defaultIndent, group(line <> render(t.p0) <> line <> render(t.p1))))

  @inline
  protected def renderBinaryOp(op: String, left: Cont, right: Cont): Cont =
    parens(text(op) <> nest(defaultIndent, group(line <> left <> line <> right)))

  @inline
  protected def renderNAryOp(op: String, terms: Term*): Cont =
    parens(text(op) <> nest(defaultIndent, group(line <> ssep((terms map render).to(collection.immutable.Seq), line))))

  @inline
  protected def renderApp(functionName: String, args: Seq[Term], outSort: Sort): Cont = {
    val docAppNoParens =
      text(sanitize(functionName)) <+> ssep((args map render).to(collection.immutable.Seq), space)

    if (args.nonEmpty)
      parens(docAppNoParens)
    else
      parens(text("as") <+> docAppNoParens <+> render(outSort))
  }

  @inline
  protected def renderSMTApp(functionName: String, args: Seq[Term], outSort: Sort) = {
    val docAppNoParens =
      text(functionName) <+> ssep((args map render).to(collection.immutable.Seq), space)

    if (args.nonEmpty)
      parens(docAppNoParens)
    else
      docAppNoParens
  }

  protected def render(q: Quantifier): Cont = q match {
    case Forall => "forall"
    case Exists => "exists"
  }

  protected def render(literal: Literal): Cont = literal match {
    case IntLiteral(n) =>
      if (n >= 0) n.toString()
      else parens(text("- 0") <+> value(-n))

    case Unit => "$Snap.unit"
    case True => "true"
    case False => "false"
    case Null => "$Ref.null"
    case _: SeqNil => renderApp("Seq_empty", Seq(), literal.sort)
    case _: EmptySet => renderApp("Set_empty", Seq(), literal.sort)
    case _: EmptyMultiset => renderApp("Multiset_empty", Seq(), literal.sort)
    case _: EmptyMap => renderApp("Map_empty", Seq(), literal.sort)
  }

  protected def renderAsReal(t: Term): Cont =
    if (t.sort == sorts.Int)
      parens(text("to_real") <+> render(t))
    else
      render(t)

  def render(id: Identifier, sanitizeIdentifier: Boolean = true): String = {
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
  }

  def reset(): Unit = {
    sanitizedNamesCache.clear()
  }

  def stop(): Unit = {
    if (sanitizedNamesCache != null) sanitizedNamesCache.clear()
  }
}
