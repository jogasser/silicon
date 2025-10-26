// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.supporters

import scala.reflect.{ClassTag, classTag}
import viper.silicon.Config
import viper.silicon.state.terms.{Sort, Term, sorts}
import viper.silicon.verifier.Verifier
import viper.silver.ast
import viper.silver.ast.{NoInfo, NoPosition, NoTrafos}

object SequencesContributor {
  lazy val rangeFun: ast.Function = {
    val i = ast.LocalVar("i", ast.Int)();
    val j = ast.LocalVar("j", ast.Int)();
    val recCall = ast.FuncApp("seq.range", Seq(ast.Sub(i, ast.IntLit(1)())(), j))(pos =NoPosition, info=NoInfo, typ=ast.SeqType(ast.Int), errT=NoTrafos)
    ast.Function("seq.range",
      Seq(ast.LocalVarDecl("i", ast.Int)(), ast.LocalVarDecl("j", ast.Int)()),
      ast.SeqType(ast.Int),
      Seq(), // pres
      Seq(
        ast.Implies(ast.GtCmp(j, i)(), ast.EqCmp(ast.SeqLength(ast.Result(ast.SeqType(ast.Int))())(), ast.Sub(j, i)())())(),
        ast.Implies(ast.Not(ast.GtCmp(j, i)())(), ast.EqCmp(ast.SeqLength(ast.Result(ast.SeqType(ast.Int))())(), ast.IntLit(0)())())(),
        ast.Implies(ast.GtCmp(j, i)(), ast.EqCmp(ast.SeqTake(ast.Result(ast.SeqType(ast.Int))(), ast.IntLit(1)())(), ast.ExplicitSeq(Seq(i))())())(),
        ast.Implies(ast.GtCmp(j, i)(), ast.EqCmp(ast.SeqDrop(ast.Result(ast.SeqType(ast.Int))(), ast.IntLit(1)())(), recCall)())()
      ), // posts
      Some(ast.CondExp(
        ast.GtCmp(j, i)(),
        ast.SeqAppend(ast.ExplicitSeq(Seq(i))(), recCall)(),
        ast.EmptySeq(ast.Int)()
      )())
    )()
  }
}

class DefaultSequencesContributor(val domainTranslator: DomainsTranslator[Term], config: Config)
    extends BuiltinDomainsContributor {

  type BuiltinDomainType = ast.SeqType
  val builtinDomainTypeTag: ClassTag[BuiltinDomainType] = classTag[ast.SeqType]

  lazy val defaultSourceResource: String = {
    if (Verifier.config.useOldAxiomatization())
      "/dafny_axioms/sequences_old.vpr"
    else
      "/dafny_axioms/sequences.vpr"
  }
  val userProvidedSourceFilepath: Option[String] = config.sequenceAxiomatizationFile.toOption
  val sourceDomainName: String = "$Seq"

  override protected def transformSourceDomainInstance(sequenceDomainInstance: ast.Domain, typ: ast.DomainType): ast.Domain = {
    // sequences.vpr (val sourceResource) contains functions and axioms for generic sequences (Seq[E]), and those
    // for integer sequences (Seq[Int]): currently, function Seq_range and corresponding axioms.
    if (typ.typVarsMap.head._2 == ast.Int) {
      sequenceDomainInstance
    } else {
      // TODO: Generalise code once more functions (and/or axioms) are affected
      val functions = sequenceDomainInstance.functions.filterNot(_.name == "Seq_range")
      val axioms = sequenceDomainInstance.axioms.filterNot(a => a.isInstanceOf[ast.NamedDomainAxiom] && a.asInstanceOf[ast.NamedDomainAxiom].name.startsWith("Seq_range_"))

      sequenceDomainInstance.copy(functions = functions, axioms = axioms)(sequenceDomainInstance.pos, sequenceDomainInstance.info, sequenceDomainInstance.errT)
    }
  }

  def targetSortFactory(argumentSorts: Iterable[Sort]): Sort = {
    assert(argumentSorts.size == 1)
    sorts.Seq(argumentSorts.head)
  }
}
