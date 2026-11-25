/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassConeCompositionFaces
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassH1MiddleJoinScalar
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassH1UnaryEvaluation
public import Colib.Topology.Prespectrum.ConeSquareCompositionCells

/-!
# First and middle Bass H₁ cells on the original pasted comparison

The two unary families evaluate to the prescribed first half and middle
rectangle of the actual pasted homotopy at every level and at both original
parameters. The common face then evaluates to both literal raw tracks.
Adapted from `BassH1NativeCells.lean` and `H1MiddleJoinFace.lean` in the original
BoundedFlat Bass proof at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Opposite Convexity Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.BaseChange.Coefficients CommRingCat.PolynomialLaurent
open CategoryTheory.Waldhausen.IteratedS FundamentalGroupoid.OpenCover
open scoped Topology unitInterval

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH1NativeCells

local notation "W" => BoundedFlatPerfectTripleSimplex.structureOn

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- Exact first half of the unchanged original pasted Bass comparison. -/
theorem first_half (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (W (space (op P, a)))).space n) :
    (boundedAboveFlatCoefficientBassCompositeComparison P u v).level n
      (leftHalf s, HomotopyPushout.cylinder
        (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P a))
        (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P a)) n (t, x)) =
      (boundedAboveFlatPerfectPullbackPrespectrumMap
        (coefficientMap P ((laurentUnderFunctor R).map v))).map n
          ((boundedAboveFlatCoefficientBassComparisonHomotopy P u).level n
            (s, HomotopyPushout.cylinder
              (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P a))
              (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P a)) n
          (t, x))) :=
  coneSquarePasted_leftHalf
    (boundedAboveFlatCoefficientBassSquareComparison P a)
    (boundedAboveFlatCoefficientBassSquareComparison P b)
    (boundedAboveFlatCoefficientBassSquareComparison P c)
    (boundedAboveFlatCoefficientPolynomialSpanMap P u)
    (boundedAboveFlatPerfectPullbackPrespectrumMap
      (coefficientMap P ((laurentUnderFunctor R).map u)))
    (boundedAboveFlatCoefficientPolynomialSpanMap P v)
    (boundedAboveFlatPerfectPullbackPrespectrumMap
      (coefficientMap P ((laurentUnderFunctor R).map v)))
    (boundedAboveFlatCoefficientBassComparisonHomotopy P u)
    (boundedAboveFlatCoefficientBassComparisonHomotopy P v) n s _

/-- Exact second half, on the actual span-u image of every original cylinder point. -/
theorem second_half (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (W (space (op P, a)))).space n) :
    (boundedAboveFlatCoefficientBassCompositeComparison P u v).level n
      (rightHalf s, HomotopyPushout.cylinder
        (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P a))
        (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P a)) n (t, x)) =
      (boundedAboveFlatCoefficientBassComparisonHomotopy P v).level n
        (s, (boundedAboveFlatCoefficientPolynomialSpanMap P u).map n
          (HomotopyPushout.cylinder
            (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P a))
            (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P a)) n (t, x))) :=
  coneSquarePasted_rightHalf
    (boundedAboveFlatCoefficientBassSquareComparison P a)
    (boundedAboveFlatCoefficientBassSquareComparison P b)
    (boundedAboveFlatCoefficientBassSquareComparison P c)
    (boundedAboveFlatCoefficientPolynomialSpanMap P u)
    (boundedAboveFlatPerfectPullbackPrespectrumMap
      (coefficientMap P ((laurentUnderFunctor R).map u)))
    (boundedAboveFlatCoefficientPolynomialSpanMap P v)
    (boundedAboveFlatPerfectPullbackPrespectrumMap
      (coefficientMap P ((laurentUnderFunctor R).map v)))
    (boundedAboveFlatCoefficientBassComparisonHomotopy P u)
    (boundedAboveFlatCoefficientBassComparisonHomotopy P v) n s _

/-- The middle quarter of the actual polynomial span gives its whole target cylinder. -/
theorem span_middle (n : ℕ) (t : unitInterval)
    (x : (originalPrespectrum (W (space (op P, a)))).space n) :
    (boundedAboveFlatCoefficientPolynomialSpanMap P u).map n
      (HomotopyPushout.cylinder
        (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P a))
        (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P a)) n
          (rightHalf (leftHalf t), x)) =
    HomotopyPushout.cylinder
      (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P b))
      (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P b)) n
        (t, (boundedAboveFlatPerfectPullbackPrespectrumMap (coefficientMap P u)).map n x) :=
  HomotopyPushout.mapOfHomotopies_middle_cell _ _ _ _ _ _ _ _ _ n t x

/-- The first whole cell of the original H₁ surface has the first component's exact family value. -/
theorem first_native (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (W (space (op P, a)))).space n) :
    prespectrumSimplexFamily (BoundedFlatCoefficientBassH1Components.firstSimplex P u v) n
      (BoundedFlatCoefficientBassH0Diagram.parameter (s, t), x) =
    (boundedAboveFlatCoefficientBassCompositeComparison P u v).level n
      (leftHalf s, HomotopyPushout.cylinder
        (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P a))
        (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P a)) n (t, x)) :=
  (BoundedFlatCoefficientBassH1Components.first_native P u v n s t x).trans
    (first_half P u v n s t x).symm

/-- The middle product-coordinate cell retains the whole original target pushout cylinder. -/
theorem middle_native (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (W (space (op P, a)))).space n) :
    prespectrumSimplexFamily (BoundedFlatCoefficientBassH1Components.middleSimplex P u v) n
      (BoundedFlatCoefficientBassH0Diagram.parameter (s, t), x) =
    (boundedAboveFlatCoefficientBassCompositeComparison P u v).level n
      (rightHalf s, HomotopyPushout.cylinder
        (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P a))
        (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P a)) n
          (rightHalf (leftHalf t), x)) := by
  rw [BoundedFlatCoefficientBassH1Components.middle_native, second_half, span_middle]

open BoundedFlatCoefficientBassH1Join

/-- Every original point of the shared H1 middle boundary is evaluated by that exact diagram. -/
theorem middle_boundary_native (n : ℕ) (t : unitInterval)
    (x : (originalPrespectrum (W (space (op P, a)))).space n) :
    prespectrumSimplexFamily (middleBoundarySimplex P u v) n
      (BoundedFlatPerfectNativeSquareFiveSimplex.parameter t, x) =
    (boundedAboveFlatCoefficientBassCompositeComparison P u v).level n
      (leftHalf 1, HomotopyPushout.cylinder
        (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P a))
        (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P a)) n
          (rightHalf (leftHalf t), x)) := by
  change prespectrumSimplexFamily
    ((BoundedFlatCoefficientBassH1Components.firstSimplex P u v).face firstMiddleFace) n
    (BoundedFlatPerfectNativeSquareFiveSimplex.parameter t, x) = _
  rw [← prespectrumSimplexFamily_face, first_middle_parameter]
  exact first_native P u v n 1 (rightHalf (leftHalf t)) x

/-- The same entire diagram retains the actual original middle-cell source values. -/
theorem middle_boundary_native_other (n : ℕ) (t : unitInterval)
    (x : (originalPrespectrum (W (space (op P, a)))).space n) :
    prespectrumSimplexFamily (middleBoundarySimplex P u v) n
      (BoundedFlatPerfectNativeSquareFiveSimplex.parameter t, x) =
    (boundedAboveFlatCoefficientBassCompositeComparison P u v).level n
      (rightHalf 0, HomotopyPushout.cylinder
        (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P a))
        (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P a)) n
          (rightHalf (leftHalf t), x)) := by
  change prespectrumSimplexFamily
    ((BoundedFlatCoefficientBassH1Components.firstSimplex P u v).face firstMiddleFace) n
    (BoundedFlatPerfectNativeSquareFiveSimplex.parameter t, x) = _
  rw [middle_face, ← prespectrumSimplexFamily_face, middle_source_parameter]
  exact middle_native P u v n 0 t x

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH1NativeCells
