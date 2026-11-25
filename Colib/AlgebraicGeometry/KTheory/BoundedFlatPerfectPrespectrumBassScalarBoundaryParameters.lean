/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumBassScalarComparison
public import Colib.KTheory.Waldhausen.Iterated.BassScalarBoundaryLiftOps
public import Colib.KTheory.Waldhausen.Iterated.ScalarChartPause

/-!
# The scalar boundary and moving-square parameters for Bass coefficient comparison

The surfaces use the original whole boundary, its three-side quotient, and
the exact terminal pause on the chart edge. Adapted from
`BassBoundarySpecialization.lean` and `BassMovingSquarePause.lean`
under `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

open Convexity Topology CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open scoped Topology unitInterval

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectDoubleSquareScalarPaths

/-- The original coefficient boundary uses the unchanged constituent chart and total paths. -/
def coefficientBoundaryParameter :=
  Path.Homotopy.boundaryOfComparison originalComparisonParameter

/-- The moving-square parameter descends through the original three-side quotient. -/
def coefficientMovingSquareParameter :
    C(unitInterval × unitInterval, StdSimplex ℝ (Fin 18)) :=
  collapsed coefficientBoundaryParameter

/-- The paused square retains the original terminal chart pause before taking the quotient. -/
def coefficientPausedSquareParameter :
    C(unitInterval × unitInterval, StdSimplex ℝ (Fin 18)) :=
  collapsed (pauseRightParameter coefficientBoundaryParameter)

end AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectDoubleSquareScalarPaths
