// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silicon.dependencyAnalysis

/**
 * The settings of the dependency analysis, which are passed explicitly to the code that needs them.
 *
 * @param enableDebugging keep all low-level details in the graph instead of merging nodes
 */
case class DependencyAnalysisOptions(enableDebugging: Boolean = false)
