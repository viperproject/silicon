/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.decider

import scala.collection.mutable
import viper.silver.ast.pretty.FastPrettyPrinterBase
import viper.silver.components.StatefulComponent
import viper.silicon.interfaces.decider.TermConverter
import viper.silicon.state.Identifier
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

  protected def render(sort: Sort): Cont = sort match {
    case sorts.Int => "Int"
    case sorts.Bool => "Bool"
    case sorts.Perm => "$Perm"
    case sorts.Snap => "$Snap"
    case sorts.Ref => "$Ref"
    case sorts.Seq(elementSort) => text("$Seq<") <> render(elementSort) <> ">"
    case sorts.Set(elementSort) => text("Set<") <> render(elementSort) <> ">"
    case sorts.Multiset(elementSort) => text("Multiset<") <> render(elementSort) <> ">"
    case sorts.UserSort(id) => sanitize(id)

    case sorts.Unit =>
      /* Sort Unit corresponds to Scala's Unit type and is used, e.g., as the
       * domain sort of nullary functions.
       */
      ""

    case sorts.FieldValueFunction(codomainSort) => text("$FVF<") <> render(codomainSort) <> ">"
    case sorts.PredicateSnapFunction(codomainSort) => text("$PSF<") <> render(codomainSort) <> ">"
  }

  def convert(d: Decl): String = {
    super.pretty(defaultWidth, render(d))
  }

  protected def render(decl: Decl): Cont = decl match {
    case SortDecl(sort: Sort) =>
      parens(text("declare-sort") <+> render(sort))

    case FunctionDecl(fun: Function) =>
      val idDoc = sanitize(fun.id)
      val argSortsDoc = fun.argSorts.map(render)
      val resultSortDoc = render(fun.resultSort)

      if (argSortsDoc.isEmpty)
        parens(text("declare-const") <+> idDoc <+> resultSortDoc)
      else
        parens(text("declare-fun") <+> idDoc <+> parens(ssep(argSortsDoc.to[collection.immutable.Seq], space)) <+> resultSortDoc)

    case SortWrapperDecl(from, to) =>
      val id = Identifier(sortWrapperName(from, to))
      val fct = FunctionDecl(Fun(id, from, to))

      render(fct)

    case MacroDecl(id, args, body) =>
      val idDoc = sanitize(id)
      val argDocs = (args map (v => parens(text(sanitize(v.id)) <+> render(v.sort)))).to[collection.immutable.Seq]
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
      sanitize(x.id)

    case fapp: Application[_] =>
      renderApp(fapp.applicable.id.name, fapp.args, fapp.sort)

    /* Split axioms with more than one trigger set into multiple copies of the same
     * axiom, each with a single trigger. This can avoid incompletenesses due to Z3
     * potentially ignoring all but the first trigger set. (I can't find the post
     * by Nikolaj now, but he described it somewhere, either on Stackoverflow or in
     * Z3's issue tracker).
     */
    case q: Quantification if q.triggers.lengthCompare(1) > 0 =>
      render(And(q.triggers.map(trg => q.copy(triggers = Vector(trg)))))

    /* Handle quantifiers that have at most one trigger set */
    case Quantification(quant, vars, body, triggers, name, _) =>
      val docVars = ssep((vars map (v => parens(text(sanitize(v.id)) <+> render(v.sort)))).to[collection.immutable.Seq], space)
      val docBody = render(body)
      val docQuant = render(quant)

      val docTriggers =
        ssep(triggers.map(trigger => ssep((trigger.p map render).to[collection.immutable.Seq], space))
                     .map(d => text(":pattern") <+> parens(d)).to[collection.immutable.Seq],
             line)

      val docQid: Cont =
        if (name.isEmpty) nil
        else s":qid |$name|"

      parens(docQuant <+> parens(docVars) <+> parens(text("!") <> nest(defaultIndent, line <> docBody <> line <> docTriggers <> line <> docQid)))

    /* Booleans */

    case uop: Not => renderUnaryOp("not", uop)
    case And(ts) => renderNAryOp("and", ts: _*)
    case Or(ts) => renderNAryOp("or", ts: _*)
    case bop: Implies => renderBinaryOp("implies", bop)
    case bop: Iff => renderBinaryOp("iff", bop)
    case bop: BuiltinEquals => renderBinaryOp("=", bop)

    case bop: CustomEquals => bop.p0.sort match {
      case _: sorts.Seq => renderBinaryOp("$Seq.equal", bop)
      case _: sorts.Set => renderApp("Set_equal", Seq(bop.p0, bop.p1), bop.sort)
      case _: sorts.Multiset => renderApp("Multiset_equal", Seq(bop.p0, bop.p1), bop.sort)
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

    case FullPerm() => "$Perm.Write"
    case NoPerm() => "$Perm.No"
    case FractionPermLiteral(r) => renderBinaryOp("/", renderAsReal(IntLiteral(r.numerator)), renderAsReal(IntLiteral(r.denominator)))
    case FractionPerm(n, d) => renderBinaryOp("/", renderAsReal(n), renderAsReal(d))
    case PermLess(t0, t1) => renderBinaryOp("<", render(t0), render(t1))
    case PermAtMost(t0, t1) => renderBinaryOp("<=", render(t0), render(t1))
    case PermPlus(t0, t1) => renderBinaryOp("+", renderAsReal(t0), renderAsReal(t1))
    case PermMinus(t0, t1) => renderBinaryOp("-", renderAsReal(t0), renderAsReal(t1))
    case PermTimes(t0, t1) => renderBinaryOp("*", renderAsReal(t0), renderAsReal(t1))
    case IntPermTimes(t0, t1) => renderBinaryOp("*", renderAsReal(t0), renderAsReal(t1))
    case PermIntDiv(t0, t1) => renderBinaryOp("/", renderAsReal(t0), renderAsReal(t1))
    case PermMin(t0, t1) => renderBinaryOp("$Perm.min", render(t0), render(t1))
    case IsValidPermVar(v) => parens(text("$Perm.isValidVar") <+> render(v))
    case IsReadPermVar(v, ub) => parens(text("$Perm.isReadVar") <+> render(v) <+> render(ub))

    /* Sequences */

    case SeqRanged(t0, t1) => renderBinaryOp("$Seq.range", render(t0), render(t1))
    case SeqSingleton(t0) => parens(text("$Seq.singleton") <+> render(t0))
    case bop: SeqAppend => renderBinaryOp("$Seq.append", bop)
    case uop: SeqLength => renderUnaryOp("$Seq.length", uop)
    case bop: SeqAt => renderBinaryOp("$Seq.index", bop)
    case bop: SeqTake => renderBinaryOp("$Seq.take", bop)
    case bop: SeqDrop => renderBinaryOp("$Seq.drop", bop)
    case bop: SeqIn => renderBinaryOp("$Seq.contains", bop)
    case SeqUpdate(t0, t1, t2) => renderNAryOp("$Seq.update", t0, t1, t2)

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



    case PredicateDomain(id, psf) => parens(text("$PSF.domain_") <> id <+> render(psf))

    case PredicateLookup(id, psf, args) =>
      val snap: Term = if (args.size == 1) {
        args.head.convert(sorts.Snap)
      } else {
        args.reduce((arg1: Term, arg2: Term) => Combine(arg1, arg2))
      }

      parens(text("$PSF.lookup_") <> id <+> render(psf) <+> render(snap))

    /* Other terms */

    case First(t) => parens(text("$Snap.first") <+> render(t))
    case Second(t) => parens(text("$Snap.second") <+> render(t))

    case bop: Combine =>
      renderBinaryOp("$Snap.combine", bop)

    case SortWrapper(t, to) =>
      parens(text(sortWrapperName(t.sort, to)) <+> render(t))

    case Distinct(symbols) =>
      parens(text("distinct") <+> ssep((symbols.toSeq map (s => sanitize(s.id): Cont)).to[collection.immutable.Seq], space))

    case Let(bindings, body) =>
      val docBindings = ssep((bindings.toSeq map (p => parens(render(p._1) <+> render(p._2)))).to[collection.immutable.Seq], space)
      parens(text("let") <+> parens(docBindings) <+> render(body))

    case _: MagicWandChunkTerm =>
      sys.error(s"Unexpected term $term cannot be translated to SMTLib code")
  }

  @inline
  protected def renderUnaryOp(op: String, t: UnaryOp[Term]) =
    parens(text(op) <> nest(defaultIndent, group(line <> render(t.p))))

  @inline
  protected def renderUnaryOp(op: String, doc: Cont) =
    parens(text(op) <> nest(defaultIndent, group(line <> doc)))

  @inline
  protected def renderBinaryOp(op: String, t: BinaryOp[Term]) =
    parens(text(op) <> nest(defaultIndent, group(line <> render(t.p0) <> line <> render(t.p1))))

  @inline
  protected def renderBinaryOp(op: String, left: Cont, right: Cont) =
    parens(text(op) <> nest(defaultIndent, group(line <> left <> line <> right)))

  @inline
  protected def renderNAryOp(op: String, terms: Term*) =
    parens(text(op) <> nest(defaultIndent, group(line <> ssep((terms map render).to[collection.immutable.Seq], line))))

  @inline
  protected def renderApp(functionName: String, args: Seq[Term], outSort: Sort) = {
    val inSorts = args map (_.sort)
    val id = Identifier(functionName)

    val docAppNoParens =
      text(sanitize(functionName)) <+> ssep((args map render).to[collection.immutable.Seq], space)

    if (args.nonEmpty)
      parens(docAppNoParens)
    else
      parens(text("as") <+> docAppNoParens <+> render(outSort))
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
    case True() => "true"
    case False() => "false"
    case Null() => "$Ref.null"
    case SeqNil(elementSort) => text("$Seq.empty<") <> render(elementSort) <> ">"
    case EmptySet(elementSort) => renderApp("Set_empty", Seq(), literal.sort)
    case EmptyMultiset(elementSort) => renderApp("Multiset_empty", Seq(), literal.sort)
  }

  protected def renderAsReal(t: Term): Cont =
    if (t.sort == sorts.Int)
      parens(text("to_real") <+> render(t))
    else
      render(t)

  protected def sortWrapperName(from: Sort, to: Sort): String =
    s"$$SortWrappers.${convert(from)}To${convert(to)}"

  @inline
  private def sanitize(id: Identifier): String = sanitize(id.name)

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
