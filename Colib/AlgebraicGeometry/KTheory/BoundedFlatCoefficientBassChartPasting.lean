/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.Util.References

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassComparisonEndpointTracks
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumDoubleSquareProjection
public import Colib.Topology.Prespectrum.RelativeHomotopySquarePasting

/-!
# Actual Laurent chart pastings in the coefficient Bass comparison

The positive and inverse charts separately use the geometric projection comparison. Their
common outer Laurent projection track is canceled by the native relative pasting comparison.
The endpoint tracks are the original charts and the chart restrictions of the raw Bass map.

Implementation provenance: Quillen `BoundedFlat/CoefficientBassMap.lean:151-164,183-202`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.BaseChange.Coefficients CommRingCat.PolynomialLaurent
universe u
namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (g : a ⟶ b)

/-- Genuine geometric pasting for the original plus coefficient tracks and common outer square. -/
def boundedAboveFlatCoefficientPlusPasting :
    (boundedAboveFlatCoefficientPlusLeftTrack P g).RelHomotopy
      (boundedAboveFlatCoefficientPlusRightTrack P g) :=
  DoubleSquareTrack.projectionComparison (polynomialProjection P a) (laurentPlus P a)
    (polynomialProjection P b) (laurentPlus P b) (coefficientMap P g)
    (coefficientMap P ((polynomialUnderFunctor R).map g))
    (coefficientMap P ((laurentUnderFunctor R).map g))
    (polynomialProjection_naturality P g)
    (coefficientMap_naturality_of_natTrans P (underToLaurent R) g)
    (laurentProjection P a) (laurentProjection P b)
    (laurentPlus_projection P a) (laurentPlus_projection P b)

/-- Genuine geometric pasting for the original minus coefficient tracks and common outer square. -/
def boundedAboveFlatCoefficientMinusPasting :
    (boundedAboveFlatCoefficientMinusLeftTrack P g).RelHomotopy
      (boundedAboveFlatCoefficientMinusRightTrack P g) :=
  DoubleSquareTrack.projectionComparison (polynomialProjection P a) (laurentMinus P a)
    (polynomialProjection P b) (laurentMinus P b) (coefficientMap P g)
    (coefficientMap P ((polynomialUnderFunctor R).map g))
    (coefficientMap P ((laurentUnderFunctor R).map g))
    (polynomialProjection_naturality P g)
    (coefficientMap_naturality_of_natTrans P (underToLaurentInvert R) g)
    (laurentProjection P a) (laurentProjection P b)
    (laurentMinus_projection P a) (laurentMinus_projection P b)

/-- The two genuine Laurent coefficient pastings cancel their common outer square and give
an actual relative boundary comparison, retaining the prescribed concatenation associations. -/
def boundedAboveFlatCoefficientBassBoundary :=
  Homotopy.RelHomotopy.pasteTwoSquares
    (boundedAboveFlatCoefficientPlusPasting P g) (boundedAboveFlatCoefficientMinusPasting P g)

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientBassMap.lean:151-202"
  "adaptation" "Both original chart-relative comparisons and their common projection cancellation."]
  boundedAboveFlatCoefficientPlusPasting
  boundedAboveFlatCoefficientMinusPasting
  boundedAboveFlatCoefficientBassBoundary

end AlgebraicGeometry.Scheme.Modules
