/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassCommonChartSimplex
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassCompositionCharts
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumBassChartScalarFaces

/-!
# Both literal raw Bass chart faces on the actual common overlap simplex

The full positive and inverse paused chart evaluations agree with their actual
raw chart-face maps after the polynomial projection. Adapted from
`Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/BassCommonChartSimplex.lean:146-171`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Opposite Convexity Topology
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open CategoryTheory.Waldhausen.IteratedS CommRingCat.PolynomialLaurent
open scoped Simplicial Topology unitInterval

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassOverlap

open BoundedFlatPerfectDoubleSquareScalarPaths (coefficientPausedSquareParameter)

local notation "W" => BoundedFlatPerfectTripleSimplex.structureOn
local notation "K" => boundedAboveFlatPerfectPullbackPrespectrumMap

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The actual paused positive chart square is retained on the original overlap. -/
theorem plusChart_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (W (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n
      (StdSimplex.map plusFace.toOrderHom
        (coefficientPausedSquareParameter (r, s)), x) =
      (boundedAboveFlatCoefficientBassCompositionPlusChart P u v).level n
        (r, (s, (K (polynomialProjection P a)).map n x)) := by
  rw [plus_family]
  change _ = ((BoundedFlatCoefficientTransformationComposition.movingSquare P
    (underToLaurent R) u v).pauseRight).level n
      (r, (s, (K (polynomialProjection P a)).map n x))
  exact BoundedFlatPerfectBassScalarComparison.plusComparisonSquare_native P u v n r s _

/-- The actual paused negative chart square is retained on the original overlap. -/
theorem minusChart_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (W (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n
      (StdSimplex.map minusFace.toOrderHom
        (coefficientPausedSquareParameter (r, s)), x) =
      (boundedAboveFlatCoefficientBassCompositionMinusChart P u v).level n
        (r, (s, (K (polynomialProjection P a)).map n x)) := by
  rw [minus_family]
  change _ = ((BoundedFlatCoefficientTransformationComposition.movingSquare P
    (underToLaurentInvert R) u v).pauseRight).level n
      (r, (s, (K (polynomialProjection P a)).map n x))
  exact BoundedFlatPerfectBassScalarComparison.minusComparisonSquare_native P u v n r s _

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassOverlap
