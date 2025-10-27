// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.rules

import viper.silicon.state._
import viper.silicon.state.terms._

object functionSupporter {
  def initialVersion(function: HeapDepFun): HeapDepFun = {
    function.id match {
      case SuffixedIdentifier(id, _, _) => HeapDepFun(id, function.argSorts, function.resultSort)
      case _ => function
    }
  }

  def limitedVersion(function: HeapDepFun): HeapDepFun = {
    val id = function.id.withSuffix("%", "limited")
    HeapDepFun(id, function.argSorts, function.resultSort)
  }

  def postconditionVersion(function: HeapDepFun): HeapDepFun = {
    val id = function.id.withSuffix("%", "posts")
    HeapDepFun(id, function.argSorts, terms.sorts.Bool)
  }

  def definitionalVersion(function: HeapDepFun): HeapDepFun = {
    val id = function.id.withSuffix("%", "def")
    HeapDepFun(id, function.argSorts, terms.sorts.Bool)
  }

  def finalVersion(function: HeapDepFun): HeapDepFun = {
    val id = function.id.withSuffix("%", "final")
    HeapDepFun(id, function.argSorts, terms.sorts.Bool)
  }
}
