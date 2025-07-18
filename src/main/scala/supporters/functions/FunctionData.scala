// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package viper.silicon.supporters.functions

import scala.annotation.unused
import com.typesafe.scalalogging.LazyLogging
import viper.silicon.state.{FunctionPreconditionTransformer, Identifier, IdentifierFactory, SimpleIdentifier, SymbolConverter}
import viper.silver.ast
import viper.silver.ast.utility.Functions
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.interfaces.FatalResult
import viper.silicon.rules.{InverseFunctions, SnapshotMapDefinition, functionSupporter}
import viper.silicon.state.terms._
import viper.silicon.state.terms.predef._
import viper.silicon.supporters.PredicateData
import viper.silicon.utils.ast.simplifyVariableName
import viper.silicon.verifier.Verifier
import viper.silicon.{Config, Map, toMap}
import viper.silver.ast.LocalVarWithVersion
import viper.silver.parser.PUnknown
import viper.silver.reporter.Reporter

/* TODO: Refactor FunctionData!
 *       Separate computations from "storing" the final results and sharing
 *       them with other components. Computations should probably be moved to the
 *       FunctionVerificationUnit.
 */
class FunctionData(val programFunction: ast.Function,
                   val height: Int,
                   val quantifiedFields: InsertionOrderedSet[ast.Field],
                   val program: ast.Program)
                  /* Note: Holding references to fixed symbol converter, identifier factory, ...
                   *       (instead of going through a verifier) is only safe if these are
                   *       either effectively independent of verifiers or if they are not used
                   *       with/in the context of different verifiers.
                   */
                  (symbolConverter: SymbolConverter,
                   expressionTranslator: HeapAccessReplacingExpressionTranslator,
                   identifierFactory: IdentifierFactory,
                   predicateData: ast.Predicate => PredicateData,
                   @unused config: Config,
                   @unused reporter: Reporter)
    extends LazyLogging {

  var phase = 0

  /*
   * Properties computed from the constructor arguments
   */

  val function: HeapDepFun = symbolConverter.toFunction(programFunction)
  val limitedFunction = functionSupporter.limitedVersion(function)

  val formalArgs: Map[ast.AbstractLocalVar, Var] = toMap(
    for (arg <- programFunction.formalArgs;
         x = arg.localVar)
    yield
      x -> Var(identifierFactory.fresh(x.name),
               symbolConverter.toSort(x.typ), false))

  val formalResult = Var(identifierFactory.fresh(programFunction.result.name),
                         symbolConverter.toSort(programFunction.result.typ), false)

  val valFormalResultExp = Option.when(Verifier.config.enableDebugging())(LocalVarWithVersion(simplifyVariableName(formalResult.id.name), programFunction.result.typ)())

  val arguments = Seq(`?s`) ++ formalArgs.values
  val argumentExps =
    if (Verifier.config.enableDebugging())
      Seq(Some(ast.LocalVar(`?s`.id.name, ast.InternalType)())) ++ formalArgs.keys.map(Some(_))
    else
      Seq.fill(1 + formalArgs.size)(None)

  /*
   * Data collected during phases 1 (well-definedness checking) and 2 (verification)
   */

  /* TODO: Analogous to fresh FVFs, Nadja records PSFs in the FunctionRecorder,
   *       but they are never used. My guess is, that QP assertions over predicates
   *       are currently not really supported (incomplete? unsound?)
   */

  private[functions] var verificationFailures: Seq[FatalResult] = Vector.empty
  private[functions] var locToSnap: Map[ast.LocationAccess, Term] = Map.empty
  private[functions] var fappToSnap: Map[ast.FuncApp, Term] = Map.empty
  private[this] var freshFvfsAndDomains: InsertionOrderedSet[SnapshotMapDefinition] = InsertionOrderedSet.empty
  private[this] var freshFieldInvs: InsertionOrderedSet[InverseFunctions] = InsertionOrderedSet.empty
  private[this] var freshConstrainedVars: InsertionOrderedSet[(Var, Term)] = InsertionOrderedSet.empty
  private[this] var freshConstraints: InsertionOrderedSet[Term] = InsertionOrderedSet.empty
  private[this] var freshSnapshots: InsertionOrderedSet[Function] = InsertionOrderedSet.empty
  private[this] var freshPathSymbols: InsertionOrderedSet[Function] = InsertionOrderedSet.empty
  private[this] var freshMacros: InsertionOrderedSet[MacroDecl] = InsertionOrderedSet.empty
  private[this] var freshSymbolsAcrossAllPhases: InsertionOrderedSet[Decl] = InsertionOrderedSet.empty

  private[functions] def getFreshFieldInvs: InsertionOrderedSet[InverseFunctions] = freshFieldInvs
  private[functions] def getFreshConstrainedVars: InsertionOrderedSet[Var] = freshConstrainedVars.map(_._1)
  private[functions] def getFreshSymbolsAcrossAllPhases: InsertionOrderedSet[Decl] = freshSymbolsAcrossAllPhases

  private[functions] def advancePhase(recorders: Seq[FunctionRecorder]): Unit = {
    assert(0 <= phase && phase <= 1, s"Cannot advance from phase $phase")

    val mergedFunctionRecorder: FunctionRecorder =
      if (recorders.isEmpty)
        NoopFunctionRecorder
      else
        recorders.tail.foldLeft(recorders.head)((summaryRec, nextRec) => summaryRec.merge(nextRec))

    locToSnap = mergedFunctionRecorder.locToSnap
    fappToSnap = mergedFunctionRecorder.fappToSnap
    freshFvfsAndDomains = mergedFunctionRecorder.freshFvfsAndDomains
    freshFieldInvs = mergedFunctionRecorder.freshFieldInvs
    freshConstrainedVars = mergedFunctionRecorder.freshConstrainedVars
    freshConstraints = mergedFunctionRecorder.freshConstraints
    freshSnapshots = mergedFunctionRecorder.freshSnapshots
    freshPathSymbols = mergedFunctionRecorder.freshPathSymbols
    freshMacros = mergedFunctionRecorder.freshMacros

    freshSymbolsAcrossAllPhases ++= freshPathSymbols map FunctionDecl
    freshSymbolsAcrossAllPhases ++= freshConstrainedVars.map(pair => FunctionDecl(pair._1))
    freshSymbolsAcrossAllPhases ++= freshSnapshots map FunctionDecl
    freshSymbolsAcrossAllPhases ++= freshFieldInvs.flatMap(i => (i.inverses ++ i.images) map FunctionDecl)
    freshSymbolsAcrossAllPhases ++= freshMacros

    freshSymbolsAcrossAllPhases ++= freshFvfsAndDomains map (fvfDef =>
      fvfDef.sm match {
        case x: Var => ConstDecl(x)
        case App(f: Function, _) => FunctionDecl(f)
        case other => sys.error(s"Unexpected SM $other of type ${other.getClass.getSimpleName}")
      })
  }

  /*
   * Properties resulting from phase 1 (well-definedness checking)
   */

  lazy val translatedPosts = {
    //assert(phase == 1, s"Postcondition axiom must be generated in phase 1, current phase is $phase")
    if (programFunction.posts.nonEmpty) {
      expressionTranslator.translatePostcondition(program, programFunction.posts, this)
    } else {
      Seq()
    }
  }

  lazy val translatedPres = {
    //assert(phase == 1, s"Postcondition axiom must be generated in phase 1, current phase is $phase")
    if (programFunction.pres.nonEmpty) {
      expressionTranslator.translatePrecondition(program, programFunction.pres, this)
    } else {
      Seq()
    }
  }

  lazy val posts: Term = {
    val combinedPosts = translatedPosts.reduceOption((a, b) => And(a, b)).getOrElse(True)

    val apps = combinedPosts.deepCollect({ case d: App if d.applicable.isInstanceOf[HeapDepFun] => d})
    var i = 0;
    val resFunMap = apps.map(f => {
      i += 1;
      f -> Var(SimpleIdentifier("res" + i), f.sort, false)
    })
    var replacedTerms = combinedPosts.replace(resFunMap.map(_._1), resFunMap.map(_._2))

    resFunMap.foreach(v => {
      val res = v._2
      val limitedF = functionSupporter.limitedVersion(v._1.applicable.asInstanceOf[HeapDepFun])

      val limitedApp = App(limitedF, v._1.args)
      val app = App(functionSupporter.postconditionVersion(v._1.applicable.asInstanceOf[HeapDepFun]), v._1.args.appended(res))

      replacedTerms = Let(res, limitedApp, And(replacedTerms, app))
    })

    replacedTerms
  }

  def getBody(usePosts: Boolean): Term = {
    val combinedPosts = translatedPosts.reduceOption((a, b) => And(a, b))
    val body = expressionTranslator.translate(program, programFunction, this).map(b => Equals(formalResult, b))
    var combinedTerm =
      if(body.isDefined && combinedPosts.isDefined)
        And(body.get, combinedPosts.get)
      else if(body.isDefined)
        body.get
      else if(combinedPosts.isDefined)
        combinedPosts.get
      else
        True

    // By assigning to the limited function we make sure our function wrapper preserves x == y when we define x = fun(a) and y = fun(a)
    combinedTerm = And(Equals(formalResult, App(functionSupporter.limitedVersion(function), arguments)), combinedTerm)

    if(translatedPres.nonEmpty)
      combinedTerm = Implies(translatedPres.reduceOption((a, b) => And(a, b)).get, combinedTerm)

    val apps = combinedTerm.deepCollect({ case d: App if d.applicable.isInstanceOf[HeapDepFun] => d})
    var i = 0;
    val resFunMap = apps.map(f => {
      i += 1;
      f -> Var(SimpleIdentifier("res" + i), f.sort, false)
    })


    var replacedTerms = combinedTerm.replace(resFunMap.map(_._1), resFunMap.map(_._2))

    resFunMap.foreach(v => {
      val res = v._2
      val args = v._1.args.map(_.replace(resFunMap.map(_._1), resFunMap.map(_._2)))
      val origFun = v._1.applicable.asInstanceOf[HeapDepFun];
      val limitedF = functionSupporter.limitedVersion(origFun)
      val limitedApp = App(limitedF, args)

      val funToCall = if (usePosts) functionSupporter.postconditionVersion(origFun) else functionSupporter.definitionalVersion(origFun)
      val app = App(funToCall, args.appended(res))
      replacedTerms = Let(res, limitedApp, And(replacedTerms, app))
    })

    replacedTerms
  }

  lazy val body: Term = {
    assert(programFunction.body.isEmpty || phase == 2, s"Definitional axiom must be generated in phase 2, current phase is $phase")
    getBody(false);
  }

  def functionPostsDeclaration(): FunctionDef = {
    FunctionDef(functionSupporter.postconditionVersion(function), arguments ++ Seq(formalResult), posts)
  }

  def recursiveDefinition(): FunctionDef = {
    FunctionDef(functionSupporter.definitionalVersion(function), arguments ++ Seq(formalResult), body)
  }
}
