// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package viper.silicon.supporters.functions

import scala.annotation.unused
import com.typesafe.scalalogging.LazyLogging
import viper.silicon.state.{Identifier, IdentifierFactory, SimpleIdentifier, SymbolConverter}
import viper.silver.ast
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

  private def generateNestedDefinitionalAxioms: InsertionOrderedSet[Term] = {
    val freshSymbols: Set[Identifier] = freshSymbolsAcrossAllPhases.map(_.id)

    val nested = (
      freshFieldInvs.flatMap(_.definitionalAxioms)
        ++ freshFvfsAndDomains.flatMap (fvfDef => fvfDef.domainDefinitions ++ fvfDef.valueDefinitions)
        ++ freshConstrainedVars.map(_._2)
        ++ freshConstraints)

    // Filter out nested definitions that contain free variables.
    // This should not happen, but currently can, due to bugs in the function axiomatisation code.
    // Fixing these bugs with the current way functions are axiomatised will be very difficult,
    // but they should be resolved with Mauro's current work on heap snapshots.
    // Once his changes are merged in, the commented warnings below should be turned into errors.
    nested.filter(term => {
      val freeVars = term.freeVariables -- arguments
      val unknownVars = freeVars.filterNot(v => freshSymbols.contains(v.id))

      //if (unknownVars.nonEmpty) {
      //  val messageText = (
      //      s"Found unexpected free variables $unknownVars "
      //    + s"in term $term during axiomatisation of function "
      //    + s"${programFunction.name}")
      //
      //  reporter report InternalWarningMessage(messageText)
      //  logger warn messageText
      //}

      unknownVars.isEmpty
    })
  }

  /*
   * Properties resulting from phase 1 (well-definedness checking)
   */

  private lazy val translatedPosts = {
    assert(phase == 1 || phase == 2, s"Postcondition axiom must be generated in phase 1 or 2, current phase is $phase")
    expressionTranslator.translatePostcondition(program, programFunction.posts, this)
  }

  private lazy val translatedPres = {
    assert(phase == 1 || phase == 2, s"Precondition axiom must be generated in phase 1 or 2, current phase is $phase")
    expressionTranslator.translatePrecondition(program, programFunction.pres, this)
  }

  private lazy val definitionalBody: Term = {
    assert(phase == 2, s"Definitional function must be generated in phase 2, current phase is $phase")
    val body = expressionTranslator.translate(program, programFunction, this).map(b => Equals(formalResult, b))
    var combinedTerm = And(body.map(_ +: translatedPosts).getOrElse(translatedPosts))

    if(translatedPres.nonEmpty)
      combinedTerm = Implies(And(translatedPres), combinedTerm)

    // add nested definitional axioms & ensure result is an actual function result
    combinedTerm = And(
        generateNestedDefinitionalAxioms ++ List(
          Equals(formalResult, App(functionSupporter.limitedVersion(function), arguments)),
          combinedTerm
        )
    )

    transformAllFunctionCalls(combinedTerm, functionSupporter.definitionalVersion)
  }

  private lazy val postsBody: Term = {
    assert(phase == 1, s"Postcondition function must be generated in phase 1, current phase is $phase")
    var combinedTerm = And(translatedPosts);

    if(translatedPres.nonEmpty)
      combinedTerm = Implies(And(translatedPres), combinedTerm)

    combinedTerm = And(Equals(formalResult, App(functionSupporter.limitedVersion(function), arguments)), combinedTerm)
    transformAllFunctionCalls(combinedTerm, functionSupporter.postconditionVersion)
  }

  def transformAllFunctionCalls(term: Term, transformer: HeapDepFun => HeapDepFun): Term = {
    val apps = term.deepCollect({ case app: App if app.applicable.isInstanceOf[HeapDepFun] &&  app.applicable.asInstanceOf[HeapDepFun] != functionSupporter.limitedVersion(app.applicable.asInstanceOf[HeapDepFun]) => app})
    var i = 0
    val resFunMap = apps.map(f => {
      i += 1
      f -> Var(SimpleIdentifier("res@" + f.applicable.id.name + "@" + i), f.sort, false)
    })

    var replacedTerms = term.replace(resFunMap.map(_._1), resFunMap.map(_._2))

    resFunMap.foreach(v => {
      val res = v._2
      val args = v._1.args.map(_.replace(resFunMap.map(_._1), resFunMap.map(_._2)))
      val origFun = v._1.applicable.asInstanceOf[HeapDepFun]
      val limitedApp = App(functionSupporter.limitedVersion(origFun), args)

      val funToCall = transformer(origFun)
      val app = App(funToCall, args.appended(res))
      replacedTerms = Let(res, limitedApp, And(replacedTerms, app))
    })

    replacedTerms
  }

  def postsVersionDef(): FunctionDef = {
    FunctionDef(functionSupporter.postconditionVersion(function), arguments ++ Seq(formalResult), postsBody)
  }

  def defVersionDef(): FunctionDef = {
    FunctionDef(functionSupporter.definitionalVersion(function), arguments ++ Seq(formalResult), definitionalBody)
  }
}
