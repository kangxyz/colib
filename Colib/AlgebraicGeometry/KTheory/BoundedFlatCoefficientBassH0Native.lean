/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassH0RectangleLift
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassComparisonDescent
public import Colib.KTheory.Waldhausen.Iterated.ProjectionPasteLift
public import Colib.KTheory.Waldhausen.Iterated.ScalarRouteExtraction

/-!
# The whole coefficient Bass comparison on the original H0 cylinder

Both chart pastings are evaluated on a shared 31-vertex model simplex. The scalar boundary
cancels the actual common outer track before the three-side collapse.
Adapted from `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/BassH0Native.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Opposite Convexity Topology Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.BaseChange.Coefficients CommRingCat.PolynomialLaurent
open CategoryTheory.Waldhausen.IteratedS
open scoped Topology unitInterval

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH0Diagram

open BoundedFlatPerfectProjectionRectangleParameters SimplexParameters

local notation "W" => BoundedFlatPerfectTripleSimplex.structureOn

/-- The full original two-chart boundary, including the actual common outer-track cancellation. -/
def boundaryParameter := Path.Homotopy.pasteProjectionSquares
  (rectangle plusFace) (rectangle minusFace)

/-- The original two-parameter cylinder face after the actual three-side square collapse. -/
def parameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 31)) :=
  collapsed boundaryParameter

variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (w : a ⟶ b)

/-- The literal original Bass boundary, including cancellation of the common outer track. -/
theorem boundary_native_lift : HomotopyLift (simplex P w) boundaryParameter
    (boundedAboveFlatCoefficientBassBoundary P w) := by
  have jp := plus_rectangle_lift P w
  have jm := minus_rectangle_lift P w
  have sp := HomotopyLift.source (simplex P w) jp
  have sm := HomotopyLift.source (simplex P w) jm
  have tp := HomotopyLift.target (simplex P w) jp
  have tm := HomotopyLift.target (simplex P w) jm
  have lLp := PathLift.trans_left (simplex P w) sp
  have lPp := PathLift.trans_right (simplex P w) sp
  have lLm := PathLift.trans_left (simplex P w) sm
  have lPm := PathLift.trans_right (simplex P w) sm
  have lDp := PathLift.symm (simplex P w) (PathLift.trans_left (simplex P w) tp)
  have lDm := PathLift.symm (simplex P w) (PathLift.trans_left (simplex P w) tm)
  simp only [Path.symm_symm, Homotopy.symm_symm] at lDp lDm
  have lT := PathLift.trans_left (simplex P w) (PathLift.trans_right (simplex P w) tp)
  have lKp := PathLift.trans_right (simplex P w) (PathLift.trans_right (simplex P w) tp)
  have lKm := PathLift.trans_right (simplex P w) (PathLift.trans_right (simplex P w) tm)
  exact HomotopyLift.pasteProjectionSquares (simplex P w)
    lDp lDm lT lLp lPp lKp lLm lPm lKm jp jm

/-- Both original ofLevels transports preserve the complete boundary family. -/
theorem desc_native_lift : HomotopyLift (simplex P w) boundaryParameter
    (boundedAboveFlatCoefficientBassDescPasting P w) := by
  intro n r s x
  exact boundary_native_lift P w n r s x

/-- Every point of the original comparison homotopy on every original cylinder input. -/
theorem native (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (W (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P w) n (parameter (s, t), x) =
      (boundedAboveFlatCoefficientBassComparisonHomotopy P w).level n
        (s, HomotopyPushout.cylinder
          (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P a))
          (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P a)) n (t, x)) := by
  rw [boundedAboveFlatCoefficientBassComparisonHomotopy_cylinder]
  exact HomotopyLift.toSquare (simplex P w) (desc_native_lift P w) n s t x

/-- The exact required H0 face of the original composition cube, with both times independent. -/
theorem composition_H0 {c : Under R} (u : a ⟶ b) (v : b ⟶ c)
    (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (W (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P (u ≫ v)) n (parameter (s, t), x) =
      (boundedAboveFlatCoefficientBassComparisonHomotopy P (u ≫ v)).level n
        (s, HomotopyPushout.cylinder
          (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P a))
          (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P a)) n (t, x)) :=
  native P (u ≫ v) n s t x

/-- The entire actual H0 family fixes the original point. -/
theorem family_point (n : ℕ) (z : StdSimplex ℝ (Fin 31)) :
    prespectrumSimplexFamily (simplex P w) n
      (z, (originalPrespectrum (W (space (op P, a)))).point n) =
      (originalPrespectrum (W (space (op P, (laurentUnderFunctor R).obj b)))).point n :=
  prespectrumSimplexFamily_point (simplex P w) n z

/-- The structure time remains separate from both H0 coordinates and all scalar parameters. -/
theorem family_structure (n : ℕ) (z : StdSimplex ℝ (Fin 31))
    (x : (originalPrespectrum (W (space (op P, a)))).space n)
    (t : unitInterval) :
    prespectrumSimplexFamily (simplex P w) (n + 1)
      (z, (originalPrespectrum
        (W (space (op P, a)))).structureMap n x t) =
    (originalPrespectrum (W (space (op P, (laurentUnderFunctor R).obj b)))).structureMap n
        (prespectrumSimplexFamily (simplex P w) n (z, x)) t :=
  prespectrumSimplexFamily_structure (simplex P w) n z x t

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH0Diagram
