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
import com.microsoft.z3.{ArithExpr, BoolExpr, Context, IntExpr, RealExpr, Expr => Z3Expr, FuncDecl => Z3FuncDecl, Sort => Z3Sort}

import scala.collection.mutable

class TermToZ3APIConverter
    extends TermConverter[Z3Expr, Z3Sort, Unit]
       with StatefulComponent {

  private var sanitizedNamesCache: mutable.Map[String, String] = _

  private val nameSanitizer = new SmtlibNameSanitizer

  private val smtlibConverter = new TermToSMTLib2Converter()

  var ctx: Context = _
  val macros = mutable.HashMap[String, (Seq[Var], Term)]()

  def convert(s: Sort): Z3Sort = convertSort(s)

  def convertId(id: Identifier, sanitizeIdentifier: Boolean = true): String = {
    smtlibConverter.render(id, sanitizeIdentifier)
  }

  lazy val snapSort = {
    /*
    (declare-datatypes (($Snap 0)) ((
    ($Snap.unit)
    ($Snap.combine ($Snap.first $Snap) ($Snap.second $Snap)))))
     */
    val unit = ctx.mkConstructor("$Snap.unit", "is_$Snap.unit", null, null, null)
    val sortArray: Array[Z3Sort] = Array(null, null)
    val combine = ctx.mkConstructor("$Snap.combine", "is_$Snap.combine", Array("$Snap.first", "$Snap.second"), sortArray, Array(0, 0))
    ctx.mkDatatypeSort("$Snap", Array(unit, combine))
  }

  def convertSort(s: Sort): Z3Sort = {
    s match {
      case sorts.Int => ctx.mkIntSort()
      case sorts.Bool => ctx.mkBoolSort()
      case sorts.Perm => ctx.mkRealSort()
      case sorts.Snap => snapSort
      case sorts.Ref => refSort
      case sorts.Map(keySort, valueSort) => ??? // text("Map") <> "<" <> doRender(keySort, true) <> "~_" <> doRender(valueSort, true) <> ">"
      case sorts.Seq(elementSort) => {
        val res = ctx.mkUninterpretedSort("Seq<" + convertSortName(elementSort) + ">")
        res
      } // text("Seq<") <> doRender(elementSort, true) <> ">"
      case sorts.Set(elementSort) => ctx.mkUninterpretedSort("Set<" + convertSortName(elementSort) + ">") // text("Set<") <> doRender(elementSort, true) <> ">"
      case sorts.Multiset(elementSort) => ctx.mkUninterpretedSort("Multiset<" + convertSortName(elementSort) + ">") //  // text("Multiset<") <> doRender(elementSort, true) <> ">"
      case sorts.UserSort(id) => ctx.mkUninterpretedSort(convertId(id)) // render(id)
      case sorts.SMTSort(id) => ??? // if (alwaysSanitize) render(id) else id.name

      case sorts.Unit =>
        /* Sort Unit corresponds to Scala's Unit type and is used, e.g., as the
         * domain sort of nullary functions.
         */
        ???

      case sorts.FieldValueFunction(codomainSort) => {
        val name = convertSortName(codomainSort)
        ctx.mkUninterpretedSort("$FVF<" + name + ">")
      } //  // text("$FVF<") <> doRender(codomainSort, true) <> ">"
      case sorts.PredicateSnapFunction(codomainSort) => ctx.mkUninterpretedSort("$PSF<" + convertSortName(codomainSort) + ">")  // text("$PSF<") <> doRender(codomainSort, true) <> ">"

      case sorts.FieldPermFunction() => ctx.mkUninterpretedSort("$FPM") // text("$FPM")
      case sorts.PredicatePermFunction() => ctx.mkUninterpretedSort("$PPM") // text("$PPM")
    }
  }

  def convertSortSymbol(s: Sort): Option[com.microsoft.z3.Symbol] = {
    s match {
      case sorts.Int => None
      case sorts.Bool => None
      case sorts.Perm => None
      case sorts.Snap => Some(ctx.mkSymbol("$Snap"))
      case sorts.Ref => Some(ctx.mkSymbol("$Ref"))
      case sorts.Map(keySort, valueSort) => ??? // text("Map") <> "<" <> doRender(keySort, true) <> "~_" <> doRender(valueSort, true) <> ">"
      case sorts.Seq(elementSort) => Some(ctx.mkSymbol("Seq<" + convertSortName(elementSort) + ">")) // text("Seq<") <> doRender(elementSort, true) <> ">"
      case sorts.Set(elementSort) => Some(ctx.mkSymbol("Set<" + convertSortName(elementSort) + ">")) // text("Set<") <> doRender(elementSort, true) <> ">"
      case sorts.Multiset(elementSort) => Some(ctx.mkSymbol("Multiset<" + convertSortName(elementSort) + ">")) //  // text("Multiset<") <> doRender(elementSort, true) <> ">"
      case sorts.UserSort(id) => Some(ctx.mkSymbol(convertId(id))) // render(id)
      case sorts.SMTSort(id) => ??? // if (alwaysSanitize) render(id) else id.name

      case sorts.Unit =>
        /* Sort Unit corresponds to Scala's Unit type and is used, e.g., as the
         * domain sort of nullary functions.
         */
        ???

      case sorts.FieldValueFunction(codomainSort) => Some(ctx.mkSymbol("$FVF<" + convertSortName(codomainSort) + ">")) //  // text("$FVF<") <> doRender(codomainSort, true) <> ">"
      case sorts.PredicateSnapFunction(codomainSort) => Some(ctx.mkSymbol("$PSF<" + convertSortName(codomainSort) + ">"))  // text("$PSF<") <> doRender(codomainSort, true) <> ">"

      case sorts.FieldPermFunction() => Some(ctx.mkSymbol("$FPM")) // text("$FPM")
      case sorts.PredicatePermFunction() => Some(ctx.mkSymbol("$PPM")) // text("$PPM")
    }
  }

  def convertSortName(sort: Sort): String = {
    smtlibConverter.convertSanitized(sort)
  }

  def convert(fd: FunctionDecl): Z3FuncDecl = {
    ctx.mkFuncDecl(convertId(fd.func.id), fd.func.argSorts.filter(s => s != viper.silicon.state.terms.sorts.Unit).map(convertSort(_)).toArray, convertSort(fd.func.resultSort))
  }

  def convertFuncSymbol(fd: FunctionDecl): com.microsoft.z3.Symbol = {
    ctx.mkSymbol(convertId(fd.func.id))
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
    d match {
      case SortDecl(sort: Sort) =>
        ??? // parens(text("declare-sort") <+> render(sort) <+> text("0"))

      case fd@FunctionDecl(fun: Function) =>
        convert(fd)


      case swd@SortWrapperDecl(from, to) =>
        //        val id = swd.id
        //        val fct = FunctionDecl(Fun(id, from, to))
        //
        //        render(fct)
        ???

      case MacroDecl(id, args, body) =>
        //val idDoc = render(id)
        //val argDocs = (args map (v => parens(text(render(v.id)) <+> render(v.sort)))).to(collection.immutable.Seq)
        //val bodySortDoc = render(body.sort)
        //val bodyDoc = render(body)

        ??? // parens(text("define-fun") <+> idDoc <+> parens(ssep(argDocs, space)) <+> bodySortDoc <> nest(defaultIndent, line <> bodyDoc))
    }
  }

  def convert(t: Term): Z3Expr = {
    convertTerm(t)
  }


  def convertTerm(term: Term): Z3Expr = term match {
    case l: Literal => {
      l match {
        case IntLiteral(n) => {
          if (n >= 0)
            ctx.mkInt(n.toString())
          else
            ctx.mkUnaryMinus(ctx.mkInt((-n).toString()))
        }
        case True() => ctx.mkTrue()
        case False() => ctx.mkFalse()
        case Null() => ctx.mkConst("$Ref.null", refSort)
        case Unit => ctx.mkConst("$Snap.unit", snapSort) //"$Snap.unit"
        case _: SeqNil => renderApp("Seq_empty", Seq(), l.sort)
        case _: EmptySet => renderApp("Set_empty", Seq(), l.sort)
        case _: EmptyMultiset => renderApp("Multiset_empty", Seq(), l.sort)
        case _: EmptyMap => renderApp("Map_empty", Seq(), l.sort)
      }
    }

    case Ite(t0, t1, t2) =>
      ctx.mkITE(convertTerm(t0).asInstanceOf[BoolExpr], convertTerm(t1), convertTerm(t2))

    case x: Var =>
      ctx.mkConst(convertId(x.id), convertSort(x.sort))

    case fapp: Application[_] =>
      fapp.applicable match {
        case _: SMTFun => renderSMTApp(convertId(fapp.applicable.id, false), fapp.args, fapp.sort)
        case _ => {
          if (macros.contains(fapp.applicable.id.name)) {
            ???
          }else {
            renderApp(convertId(fapp.applicable.id), fapp.args, fapp.sort)
          }
        }
      }


    /* Handle quantifiers that have at most one trigger set */
    case Quantification(quant, vars, body, triggers, name, _) => {
      if (vars.isEmpty)
        sys.error("wtf")
      val qvarExprs = vars.map(v => convert(v)).toArray
      val patterns = triggers.map(t => ctx.mkPattern(t.p.map(convertTerm): _*)).toArray
      if (quant == Forall) {
        ctx.mkForall(qvarExprs, convertTerm(body), 1, patterns, null, ctx.mkSymbol(name), null)
      }else{
        ctx.mkExists(qvarExprs, convertTerm(body), 1, patterns, null, ctx.mkSymbol(name), null)
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
      case _: sorts.Seq => renderApp("Seq_equal", Seq(bop.p0, bop.p1), bop.sort)
      case _: sorts.Set => renderApp("Set_equal", Seq(bop.p0, bop.p1), bop.sort)
      case _: sorts.Multiset => renderApp("Multiset_equal", Seq(bop.p0, bop.p1), bop.sort)
      case _: sorts.Map => renderApp("Map_equal", Seq(bop.p0, bop.p1), bop.sort)
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


    case FullPerm() => ctx.mkConst("$Perm.Write", permSort)
    case NoPerm() => ctx.mkConst("$Perm.No", permSort)
    case FractionPermLiteral(r) => ctx.mkDiv(renderAsReal(IntLiteral(r.numerator)), renderAsReal(IntLiteral(r.denominator)))
    case FractionPerm(n, d) => ctx.mkDiv(renderAsReal(n), renderAsReal(d))
    case PermLess(t0, t1) => ctx.mkLt(convertTerm(t0).asInstanceOf[ArithExpr], convertTerm(t1).asInstanceOf[ArithExpr])
    case PermAtMost(t0, t1) => ctx.mkLe(convertTerm(t0).asInstanceOf[ArithExpr], convertTerm(t1).asInstanceOf[ArithExpr])
    case PermPlus(t0, t1) => ctx.mkAdd(convertTerm(t0).asInstanceOf[ArithExpr], convertTerm(t1).asInstanceOf[ArithExpr])
    case PermMinus(t0, t1) => ctx.mkSub(convertTerm(t0).asInstanceOf[ArithExpr], convertTerm(t1).asInstanceOf[ArithExpr])
    case PermTimes(t0, t1) => ctx.mkMul(convertTerm(t0).asInstanceOf[ArithExpr], convertTerm(t1).asInstanceOf[ArithExpr])
    case IntPermTimes(t0, t1) => ctx.mkMul(convertTerm(t0).asInstanceOf[ArithExpr], convertTerm(t1).asInstanceOf[ArithExpr])
    case PermIntDiv(t0, t1) => ctx.mkDiv(renderAsReal(t0), renderAsReal(t1))
    case PermPermDiv(t0, t1) => ctx.mkDiv(renderAsReal(t0), renderAsReal(t1))
    case PermMin(t0, t1) => renderApp("$Perm.min", Seq(t0, t1), term.sort)
    case IsValidPermVar(v) => renderApp("$Perm.isValidVar", Seq(v), term.sort)
    case IsReadPermVar(v) => renderApp("$Perm.isReadVar", Seq(v), term.sort)

    /* Sequences */

    case SeqRanged(t0, t1) => renderApp("Seq_range", Seq(t0, t1), term.sort)
    case SeqSingleton(t0) => renderApp("Seq_singleton", Seq(t0), term.sort)
    case bop: SeqAppend => renderApp("Seq_append", Seq(bop.p0, bop.p1), term.sort)
    case uop: SeqLength => renderApp("Seq_length", Seq(uop.p), term.sort)
    case bop: SeqAt => renderApp("Seq_index", Seq(bop.p0, bop.p1), term.sort)
    case bop: SeqTake => renderApp("Seq_take", Seq(bop.p0, bop.p1), term.sort)
    case bop: SeqDrop => renderApp("Seq_drop", Seq(bop.p0, bop.p1), term.sort)
    case bop: SeqIn => renderApp("Seq_contains", Seq(bop.p0, bop.p1), term.sort)
    case SeqUpdate(t0, t1, t2) => renderApp("Seq_update", Seq(t0, t1, t2), term.sort)

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

    case Domain(id, fvf) => ??? //parens(text("$FVF.domain_") <> id <+> render(fvf))

    case Lookup(field, fvf, at) =>
        ??? // parens(text("$FVF.lookup_") <> field <+> render(fvf) <+> render(at))

//    case FieldTrigger(field, fvf, at) => parens(text("$FVF.loc_") <> field <+> (fvf.sort match {
//      case sorts.FieldValueFunction(_) => render(Lookup(field, fvf, at)) <+> render(at)
//      case _ => render(fvf) <+> render(at)
//    }))
//
//    case PermLookup(field, pm, at) => parens(text("$FVF.perm_") <> field <+> render(pm) <+> render(at))
//
//    case PredicateDomain(id, psf) => parens(text("$PSF.domain_") <> id <+> render(psf))
//
//    case PredicateLookup(id, psf, args) =>
//      val snap: Term = toSnapTree(args)
//
//      parens(text("$PSF.lookup_") <> id <+> render(psf) <+> render(snap))
//
//    case PredicateTrigger(id, psf, args) =>
//      val snap: Term = toSnapTree(args)
//
//      parens(text("$PSF.loc_") <> id <+> render(PredicateLookup(id, psf, args)) <+> render(snap))
//
//    case PredicatePermLookup(predname, pm, args) =>
//      val snap: Term = toSnapTree(args)
//
//      parens(text("$PSF.perm_") <> predname <+> render(pm) <+> render(snap))
//
    /* Other terms */

    case First(t) => renderApp("$Snap.first", Seq(t), term.sort)//parens(text("$Snap.first") <+> render(t))
    case Second(t) => renderApp("$Snap.second", Seq(t), term.sort)

    case bop: Combine =>
      renderApp("$Snap.combine", Seq(bop.p0, bop.p1), term.sort)

    case SortWrapper(t, to) =>
      renderApp(convertId(SortWrapperId(t.sort, to)), Seq(t), to)
      //parens(text(render(SortWrapperId(t.sort, to))) <+> render(t))

//    case Distinct(symbols) =>
//      parens(text("distinct") <+> ssep((symbols.toSeq map (s => render(s.id): Cont)).to(collection.immutable.Seq), space))
//
//    case Let(bindings, body) =>
//      val docBindings = ssep((bindings.toSeq map (p => parens(render(p._1) <+> render(p._2)))).to(collection.immutable.Seq), space)
//      parens(text("let") <+> parens(docBindings) <+> render(body))
//
//    case _: MagicWandChunkTerm
//       | _: Quantification =>
//      sys.error(s"Unexpected term $term cannot be translated to SMTLib code")
  }

//  @inline
//  protected def renderUnaryOp(op: String, t: UnaryOp[Term]): Cont =
//    parens(text(op) <> nest(defaultIndent, group(line <> render(t.p))))
//
//  @inline
//  protected def renderUnaryOp(op: String, doc: Cont): Cont =
//    parens(text(op) <> nest(defaultIndent, group(line <> doc)))
//
//  @inline
//  protected def renderBinaryOp(op: String, t: BinaryOp[Term]): Cont =
//    parens(text(op) <> nest(defaultIndent, group(line <> render(t.p0) <> line <> render(t.p1))))
//
//  @inline
//  protected def renderBinaryOp(op: String, left: Cont, right: Cont): Cont =
//    parens(text(op) <> nest(defaultIndent, group(line <> left <> line <> right)))
//
//  @inline
//  protected def renderNAryOp(op: String, terms: Term*): Cont =
//    parens(text(op) <> nest(defaultIndent, group(line <> ssep((terms map render).to(collection.immutable.Seq), line))))
//
  @inline
  protected def renderApp(functionName: String, args: Seq[Term], outSort: Sort): Z3Expr = {
    ctx.mkApp(ctx.mkFuncDecl(functionName, args.map(a => convertSort(a.sort)).toArray, convertSort(outSort)), args.map(convertTerm(_)): _*)
  }

  lazy val permSort: Z3Sort = {
    ctx.mkRealSort()
  }

  lazy val refSort: Z3Sort = {
    ctx.mkUninterpretedSort("$Ref")
  }

  @inline
  protected def renderSMTApp(functionName: String, args: Seq[Term], outSort: Sort): Z3Expr = {
//    val docAppNoParens =
//      text(functionName) <+> ssep((args map render).to(collection.immutable.Seq), space)
//
//    if (args.nonEmpty)
//      parens(docAppNoParens)
//    else
//      parens(text("as") <+> docAppNoParens <+> render(outSort))
    // TODO: this needs to be special-cased unfortunately. Urgh.
    ???
  }

//  protected def render(q: Quantifier): Cont = q match {
//    case Forall => "forall"
//    case Exists => "exists"
//  }
//


  protected def renderAsReal(t: Term): RealExpr =
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
    sanitizedNamesCache.clear()
    macros.clear()
  }

  def stop(): Unit = {
    if (sanitizedNamesCache != null) sanitizedNamesCache.clear()
  }

  override def convertSanitized(s: Sort): Z3Sort = convertSort(s)
}
