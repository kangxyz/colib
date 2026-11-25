/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientTransformationComposition

/-!
# The literal polynomial projection square under binary composition

The full relative comparison for the fixed polynomial inclusion uses the actual
source and target tracks of the original coefficient diagram. Adapted from
`Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientBassCoherence.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace Opposite
open CategoryTheory.Waldhausen.IteratedS Topology Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.BaseChange.Coefficients CommRingCat.PolynomialLaurent
open scoped Topology unitInterval

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b c : Under R}
  (u : a ⟶ b) (v : b ⟶ c)

open BoundedFlatCoefficientTransformationComposition in
/-- The existing rectangle comparison in the polynomial coefficient-composition direction. -/
abbrev boundedAboveFlatCoefficientPolynomialTransposedRectangle :=
  rectangle P (polynomialUnderCoefficient R) u v

open BoundedFlatCoefficientTransformationComposition in
/-- The two successive original polynomial squares, with literal association casts. -/
abbrev boundedAboveFlatCoefficientPolynomialCompositeSquare :=
  compositeSquare P (polynomialUnderCoefficient R) u v

open BoundedFlatCoefficientTransformationComposition in
/-- Original source-fiber composition followed by the unchanged target projection. -/
abbrev boundedAboveFlatCoefficientPolynomialSourceCompositionTrack :=
  sourceComposition P (polynomialUnderCoefficient R) u v

open BoundedFlatCoefficientTransformationComposition in
/-- Original polynomial composition, precomposed by the unchanged source projection. -/
abbrev boundedAboveFlatCoefficientPolynomialTargetCompositionTrack :=
  targetComposition P (polynomialUnderCoefficient R) u v

/-- The two successive literal polynomial squares give the source of the transposed rectangle. -/
theorem boundedAboveFlatCoefficientPolynomialTransposedRectangle_source_level (n : ℕ) :
    (boundedAboveFlatCoefficientPolynomialCompositeSquare P u v).level n =
      (((boundedAboveFlatCoefficientPolynomialTransposedRectangle P u v).symmPath).at 0).level n :=
  BoundedFlatCoefficientTransformationComposition.rectangle_source_level P
    (polynomialUnderCoefficient R) u v n

open BoundedFlatCoefficientTransformationComposition in
/-- The entire target is the direct polynomial square and the actual two composition tracks. -/
theorem boundedAboveFlatCoefficientPolynomialTransposedRectangle_target_level (n : ℕ) :
    (((boundedAboveFlatCoefficientPolynomialTargetCompositionTrack P u v).symm.trans
      (square P (polynomialUnderCoefficient R) (u ≫ v))).trans
      (boundedAboveFlatCoefficientPolynomialSourceCompositionTrack P u v)).level n =
      (((boundedAboveFlatCoefficientPolynomialTransposedRectangle P u v).symmPath).at 1).level n :=
  rectangle_target_level P (polynomialUnderCoefficient R) u v n

open BoundedFlatCoefficientTransformationComposition in
/-- The full relative polynomial composition comparison retains the original tracks. -/
abbrev boundedAboveFlatCoefficientPolynomialSquareCompositionComparison :=
  comparison P (polynomialUnderCoefficient R) u v

/-- Both time coordinates, including at level zero, are those of the actual transposed rectangle. -/
theorem boundedAboveFlatCoefficientPolynomialSquareCompositionComparison_apply
    (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum
      (boundedAboveFlatPerfectWaldhausen (space (op P, a)).toRingedSpace)).space n) :
    (boundedAboveFlatCoefficientPolynomialSquareCompositionComparison P u v).level n
      (r, (s, x)) =
    (boundedAboveFlatCoefficientPolynomialTransposedRectangle P u v).symmPath.level n
      (r, (s, x)) := rfl

end AlgebraicGeometry.Scheme.Modules
