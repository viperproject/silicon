/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon
package decider

import org.kiama.output.PrettyPrinter
import interfaces.decider.TermConverter
import state.terms._

class TermToSMTLib2Converter extends PrettyPrinter with TermConverter[String, String, String] {
  override val defaultIndent = 2
  override val defaultWidth = 80

  lazy val uninitialized: Doc = value("<not initialized>")

  def convert(s: Sort): String = {
    super.pretty(render(s))
  }

  protected def render(sort: Sort): Doc = sort match {
    case sorts.Int => "Int"
    case sorts.Bool => "Bool"
    case sorts.Perm => "$Perm"
    case sorts.Snap => "$Snap"
    case sorts.Ref => "$Ref"
    case sorts.Seq(elementSort) => "$Seq<" <> render(elementSort) <> ">"
    case sorts.Set(elementSort) => "$Set<" <> render(elementSort) <> ">"
    case sorts.Multiset(elementSort) => "$Multiset<" <> render(elementSort) <> ">"
    case sorts.UserSort(id) => sanitizeSymbol(id)

    case a: sorts.Arrow =>
      val inStr = a.from match {
        case Seq(sorts.Unit) => ""
        case ss => ss.map(render).mkString("(", " ", ")")
      }

      inStr <+> render(a.to)

    case sorts.Unit =>
      /* Sort Unit corresponds to Scala's Unit type and is used, e.g., as the
       * domain sort of nullary functions.
       */
      ""
  }

  def convert(d: Decl): String = {
    super.pretty(render(d))
  }

  protected def render(decl: Decl): Doc = decl match {
    case SortDecl(sort: Sort) =>
      parens("declare-sort" <+> render(sort))

    case VarDecl(v: Var) =>
      parens("declare-const" <+> sanitizeSymbol(v.id) <+> render(v.sort))

    case FunctionDecl(Function(id, sort)) =>
      val idDoc = sanitizeSymbol(id)
      val inSortDoc = sort.from.map(render)
      val outSortDoc = render(sort.to)

      parens("declare-fun" <+> idDoc <+> parens(ssep(inSortDoc, space)) <+> outSortDoc)

    case SortWrapperDecl(from, to) =>
      val symbol = sortWrapperSymbol(from, to)
      val fct = FunctionDecl(Function(symbol, from :: Nil, to))

      render(fct)
  }

  def convert(t: Term): String = {
    super.pretty(render(t))
  }

  protected def render(term: Term): Doc =  term match {
    case s: Symbol => sanitizeSymbol(s.id)
    case lit: Literal => render(lit)

    case Ite(t0, t1, t2) =>
      renderNAryOp("ite", t0, t1, t2)

    case app @ Apply(f, args) =>
      val docF = render(f)

      app.funcSort.from match {
        case Seq(sorts.Unit) => docF
        case _ => parens(docF <+> ssep(args map render, space))
      }

    case FApp(f, s, tArgs) =>
      parens(sanitizeSymbol(f.id) <+> render(s) <+> ssep(tArgs map render, space))

    case Quantification(quant, vars, body, triggers, name) =>
      val docVars = ssep(vars map (v => parens(sanitizeSymbol(v.id) <+> render(v.sort))), space)
      val docBody = render(body)
      val docQuant = render(quant)

      val docTriggers =
        ssep(triggers.map(trigger => ssep(trigger.p map render, space))
                     .map(d => ":pattern" <+> parens(d)),
             line)

      val docQid: Doc =
        if (name.isEmpty) empty
        else s":qid |$name|"

      parens(docQuant <+> parens(docVars) <+> parens("!" <> nest(line <> docBody <> line <> docTriggers <> line <> docQid)))

    /* Booleans */

    case uop: Not => renderUnaryOp("not", uop)
    case And(ts) => renderNAryOp("and", ts: _*)
    case Or(ts) => renderNAryOp("or", ts: _*)
    case bop: Implies => renderBinaryOp("implies", bop)
    case bop: Iff => renderBinaryOp("iff", bop)
    case bop: BuiltinEquals => renderBinaryOp("=", bop)

    case bop: CustomEquals => bop.p0.sort match {
      case _: sorts.Seq => renderBinaryOp("$Seq.equal", bop)
      case _: sorts.Set => renderBinaryOp("$Set.equal", bop)
      case _: sorts.Multiset => renderBinaryOp("$Multiset.equal", bop)
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
    case WildcardPerm(v) => render(v)
    case FractionPerm(n, d) => renderBinaryOp("/", renderAsReal(n), renderAsReal(d))
    case PermLess(t0, t1) => renderBinaryOp("<", render(t0), render(t1))
    case PermPlus(t0, t1) => renderBinaryOp("+", renderAsReal(t0), renderAsReal(t1))
    case PermMinus(t0, t1) => renderBinaryOp("-", renderAsReal(t0), renderAsReal(t1))
    case PermTimes(t0, t1) => renderBinaryOp("*", renderAsReal(t0), renderAsReal(t1))
    case IntPermTimes(t0, t1) => renderBinaryOp("*", renderAsReal(t0), renderAsReal(t1))
    case PermIntDiv(t0, t1) => renderBinaryOp("/", renderAsReal(t0), renderAsReal(t1))
    case PermMin(t0, t1) => renderBinaryOp("$Perm.min", render(t0), render(t1))
    case IsValidPermVar(v) => parens("$Perm.isValidVar" <+> render(v))
    case IsReadPermVar(v, ub) => parens("$Perm.isReadVar" <+> render(v) <+> render(ub))


    /* Sequences */

    case SeqRanged(t0, t1) => renderBinaryOp("$Seq.range", render(t0), render(t1))
    case SeqSingleton(t0) => parens("$Seq.singleton" <+> render(t0))
    case bop: SeqAppend => renderBinaryOp("$Seq.append", bop)
    case uop: SeqLength => renderUnaryOp("$Seq.length", uop)
    case bop: SeqAt => renderBinaryOp("$Seq.index", bop)
    case bop: SeqTake => renderBinaryOp("$Seq.take", bop)
    case bop: SeqDrop => renderBinaryOp("$Seq.drop", bop)
    case bop: SeqIn => renderBinaryOp("$Seq.contains", bop)
    case SeqUpdate(t0, t1, t2) => renderNAryOp("$Seq.update", t0, t1, t2)

    /* Sets */

    case SingletonSet(t0) => parens("$Set.singleton " <+> render(t0))
    case bop: SetAdd => renderBinaryOp("$Set.unionone", bop)
    case uop: SetCardinality => renderUnaryOp("$Set.card", uop)
    case bop: SetDifference => renderBinaryOp("$Set.difference", bop)
    case bop: SetIntersection => renderBinaryOp("$Set.intersection", bop)
    case bop: SetUnion => renderBinaryOp("$Set.union", bop)
    case bop: SetIn =>
      renderBinaryOp("$Set.in", bop)
//      val expandedTerm = SetSubset(SingletonSet(bop.p0), bop.p1)
//      render(expandedTerm)
//      renderBinaryOp("$Map.select", render(bop.p1), render(bop.p0))
    case bop: SetSubset => renderBinaryOp("$Set.subset", bop)
    case bop: SetDisjoint => renderBinaryOp("$Set.disjoint", bop)

    /* Multisets */

    case SingletonMultiset(t0) => parens("$Multiset.singleton" <+> render(t0))
    case bop: MultisetAdd => renderBinaryOp("$Multiset.unionone", bop)
    case uop: MultisetCardinality => renderUnaryOp("$Multiset.card", uop)
    case bop: MultisetDifference => renderBinaryOp("$Multiset.difference", bop)
    case bop: MultisetIntersection => renderBinaryOp("$Multiset.intersection", bop)
    case bop: MultisetUnion => renderBinaryOp("$Multiset.union", bop)
    case bop: MultisetSubset => renderBinaryOp("$Multiset.subset", bop)
    case bop: MultisetCount => renderBinaryOp("$Multiset.count", bop)

    /* Domains */

    case DomainFApp(f, ts) =>
      val docArgs = ssep(ts map render, space)
      val docId = sanitizeSymbol(f.id)

      if (ts.isEmpty) docId
      else parens(docId <+> docArgs)

    /* Other terms */

    case First(t) => parens("$Snap.first" <+> render(t))
    case Second(t) => parens("$Snap.second" <+> render(t))

    case bop: Combine =>
      renderBinaryOp("$Snap.combine", bop)

    case SortWrapper(t, to) =>
      parens(sortWrapperSymbol(t.sort, to) <+> render(t))

    case Distinct(symbols) =>
      parens("distinct" <+> ssep(symbols.toSeq map render, space))

    case Let(bindings, body) =>
      val docBindings = ssep(bindings.toSeq map (p => parens(render(p._1) <+> render(p._2))), space)
      parens("let" <+> parens(docBindings) <+> render(body))
  }

  @inline
  protected def renderUnaryOp(op: String, t: UnaryOp[Term]) =
    parens(op <> nest(group(line <> render(t.p))))

  @inline
  protected def renderUnaryOp(op: String, doc: Doc) =
    parens(op <> nest(group(line <> doc)))

  @inline
  protected def renderBinaryOp(op: String, t: BinaryOp[Term]) =
    parens(op <> nest(group(line <> render(t.p0) <> line <> render(t.p1))))

  @inline
  protected def renderBinaryOp(op: String, left: Doc, right: Doc) =
    parens(op <> nest(group(line <> left <> line <> right)))

  @inline
  protected def renderNAryOp(op: String, terms: Term*) =
    parens(op <> nest(group(line <> ssep(terms map render, line))))

  protected def render(q: Quantifier): Doc = q match {
    case Forall => "forall"
    case Exists => "exists"
  }

  protected def render(literal: Literal): Doc = literal match {
    case IntLiteral(n) =>
      if (n >= 0) n.toString()
      else parens("- 0" <+> value(-n))

    case Unit => "$Snap.unit"
    case True() => "true"
    case False() => "false"
    case Null() => "$Ref.null"
    case SeqNil(elementSort) => "$Seq.empty<" <> render(elementSort) <> ">"
    case EmptySet(elementSort) => "$Set.empty<" <> render(elementSort) <> ">"
    case EmptyMultiset(elementSort) => "$Multiset.empty<" <> render(elementSort) <> ">"
  }

  protected def renderAsReal(t: Term): Doc =
    if (t.sort == sorts.Int)
      parens("to_real" <+> render(t))
    else
      render(t)

  protected def sortWrapperSymbol(from: Sort, to: Sort): String =
    s"$$SortWrappers.${convert(from)}To${convert(to)}"

  def sanitizeSymbol(str: String) = {
    val str1 = replaceOffendingCharacters(str)

    val str2 =
      if (isSafe(str1)) str1
      else "$" + str1
        /* TODO: '$' should ONLY be used to sanitise symbols, it should no longer
         *       be used to mark symbols from Silicon's preamble such as $Perm or
         *       $Seq. If need be, there should be a dedicated symbol for the
         *       former and one for the latter purpose.
         */

    str2
  }

  def replaceOffendingCharacters(str: String) =
    str.replace('#', '_')
       .replace("τ", "$tau")
       .replace('[', '<')
       .replace(']', '>')
       .replace("::", ".")
       .replace(',', '~')
       .replace(" ", "")

  /* TODO: Would be ideal if we had a list of all reserved keywords from
   *       SMTLIB2 plus those from Z3.
   */
  def isSafe(str: String) = (
      str.head == '$'
    | str.contains('<')
    | str.contains('@')
  )
}
