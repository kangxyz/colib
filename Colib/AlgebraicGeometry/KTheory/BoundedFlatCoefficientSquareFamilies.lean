/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientLaurentUnitSquares
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumSquareFivePath

/-! Whole original polynomial and Laurent-chart square families before any overlap restriction. -/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open scoped Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientSquareFamilies
local notation "W" => BoundedFlatPerfectTripleSimplex.structureOn

variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (w : a ⟶ b)

/-- The source model map for the polynomial projection naturality square of `w`. -/
abbrev polynomialSource := BoundedFlatPerfectNativeSquareFiveSimplex.source
  (coefficientMap P ((polynomialUnderFunctor R).map w)) (polynomialProjection P a)
/-- The five nodes and their references for the polynomial projection naturality square of `w`. -/
abbrev polynomialNodes := BoundedFlatPerfectNativeSquareFiveSimplex.nodes
  (coefficientMap P ((polynomialUnderFunctor R).map w)) (polynomialProjection P a)
  (polynomialProjection P b) (coefficientMap P w)
  (polynomialProjection_naturality P w)
/-- The 4-simplex encoding the polynomial projection naturality square of `w`. -/
abbrev polynomialSimplex := BoundedFlatPerfectNativeSquareFiveSimplex.simplex
  (coefficientMap P ((polynomialUnderFunctor R).map w)) (polynomialProjection P a)
  (polynomialProjection P b) (coefficientMap P w)
  (polynomialProjection_naturality P w)

variable (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
/-- The source model map for the coefficient naturality square of the chart `α` and arrow `w`. -/
abbrev chartSource := BoundedFlatPerfectNativeSquareFiveSimplex.source
  (coefficientMap P ((laurentUnderFunctor R).map w)) (coefficientMap P (α.app a))
/-- The five nodes and their references for the coefficient naturality square of `α` and `w`. -/
abbrev chartNodes := BoundedFlatPerfectNativeSquareFiveSimplex.nodes
  (coefficientMap P ((laurentUnderFunctor R).map w)) (coefficientMap P (α.app a))
  (coefficientMap P (α.app b)) (coefficientMap P ((polynomialUnderFunctor R).map w))
  (coefficientMap_naturality_of_natTrans P α w)
/-- The 4-simplex encoding the coefficient naturality square of the chart `α` and arrow `w`. -/
abbrev chartSimplex := BoundedFlatPerfectNativeSquareFiveSimplex.simplex
  (coefficientMap P ((laurentUnderFunctor R).map w)) (coefficientMap P (α.app a))
  (coefficientMap P (α.app b)) (coefficientMap P ((polynomialUnderFunctor R).map w))
  (coefficientMap_naturality_of_natTrans P α w)

/-- The whole original polynomial square, on every original source input and level. -/
theorem polynomial_native (n : ℕ) (t : unitInterval)
    (x : (originalPrespectrum (W (space (op P, a)))).space n) :
    prespectrumSimplexFamily (polynomialSimplex P w) n
      (BoundedFlatPerfectNativeSquareFiveSimplex.parameter t, x) =
      (boundedAboveFlatCoefficientPolynomialSquareHomotopy P w).level n (t, x) :=
  BoundedFlatPerfectNativeSquareFiveSimplex.native _ _ _ _ _ n t x

/-- The whole positive square accepts arbitrary polynomial-chart inputs, before projection. -/
theorem plus_native (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (W
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    prespectrumSimplexFamily (chartSimplex P w (underToLaurent R)) n
      (BoundedFlatPerfectNativeSquareFiveSimplex.parameter s, x) =
      (boundedAboveFlatCoefficientPlusSquareHomotopy P w).level n (s, x) :=
  BoundedFlatPerfectNativeSquareFiveSimplex.native _ _ _ _ _ n s x

/-- The separate inverse square likewise retains every arbitrary polynomial-chart input. -/
theorem minus_native (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (W
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    prespectrumSimplexFamily (chartSimplex P w (underToLaurentInvert R)) n
      (BoundedFlatPerfectNativeSquareFiveSimplex.parameter s, x) =
      (boundedAboveFlatCoefficientMinusSquareHomotopy P w).level n (s, x) :=
  BoundedFlatPerfectNativeSquareFiveSimplex.native _ _ _ _ _ n s x

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientSquareFamilies
