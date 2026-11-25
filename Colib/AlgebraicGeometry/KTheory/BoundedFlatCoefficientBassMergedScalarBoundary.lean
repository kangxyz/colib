/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassCommonChartFaces
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassMergedBoundarySimplex
public import Colib.Topology.Homotopy.OpenCover.TransParameters

/-!
# Scalar parameters of the actual merged Bass 44-simplex

The signed chart parameters and actual Laurent product retain their original
speeds and meet at the two separately prescribed Laurent boundaries.
Adapted from `BassMergedScalarBoundary.lean`, `BassBottomSharedScalarPaths.lean`
and `SimplexCollapsedBoundary.lean` in Quillen at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Opposite Convexity Topology Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.BaseChange.Coefficients CommRingCat.PolynomialLaurent
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open FundamentalGroupoid.OpenCover
open scoped Simplicial Topology unitInterval

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassReferenceMerge

open BoundedFlatPerfectDoubleSquareScalarPaths

local notation "W" => BoundedFlatPerfectTripleSimplex.structureOn
local notation "K" => boundedAboveFlatPerfectPullbackPrespectrumMap

private theorem collapsed_left_path {k : ℕ} {a₀ b₀ a₁ b₁ : StdSimplex ℝ (Fin (k + 1))}
    {p : Path a₀ b₀} {l : Path a₀ a₁} {q : Path a₁ b₁} {m : Path b₀ b₁}
    (J : p.Homotopy ((l.trans q).trans m.symm)) (r : unitInterval) :
    collapsed J (r, 0) = l r := by
  rw [← ThreeSideSquare.collapse_leftTime r, collapsed_collapse, J.apply_one]
  have h : ThreeSideSquare.leftTime r = leftHalf (leftHalf r) := by
    apply Subtype.ext
    simp only [coe_leftHalf]
    dsimp [ThreeSideSquare.leftTime]
    ring
  rw [h]
  exact (trans_leftHalf (l.trans q) m.symm (leftHalf r)).trans (trans_leftHalf l q r)

private theorem coefficientPausedSquareParameter_left (r : unitInterval) :
    coefficientPausedSquareParameter (r, 0) = targetChart r :=
  collapsed_left_path _ r

/-- The full positive boundary path of the actual bottom parameter, with its original speed. -/
private theorem bottom_parameter_left (r : unitInterval) :
    BoundedFlatCoefficientBassLaurentBottomFace.parameter.{u} (r, 0) =
      binaryPath (k := 14) 6 7 8 r := by
  change SimplexGrid.parameter.{u + 1} 4 2
    (BoundedFlatCoefficientBassProjectionPath.parameter 0, binaryPath (k := 2) 0 1 2 r) = _
  rw [Path.source, SimplexGrid.parameter_row]
  exact map_binaryPath (SimplexGrid.rowFace 4 2 2) 0 1 2 r

/-- The full negative boundary path of the same bottom parameter. -/
private theorem bottom_parameter_right (r : unitInterval) :
    BoundedFlatCoefficientBassLaurentBottomFace.parameter.{u} (r, 1) =
      binaryPath (k := 14) 12 13 14 r := by
  change SimplexGrid.parameter.{u + 1} 4 2
    (BoundedFlatCoefficientBassProjectionPath.parameter 1, binaryPath (k := 2) 0 1 2 r) = _
  rw [Path.target, SimplexGrid.parameter_row]
  exact map_binaryPath (SimplexGrid.rowFace 4 2 4) 0 1 2 r


/-- The fixed positive chart's whole bottom edge selects these exact common-chart nodes. -/
private theorem plus_lower_parameter (r : unitInterval) :
    StdSimplex.map BoundedFlatCoefficientBassOverlap.plusFace.toOrderHom
      (coefficientPausedSquareParameter (r, 0)) =
        binaryPath (k := 35) 15 16 17 r := by
  rw [coefficientPausedSquareParameter_left]
  exact map_binaryPath BoundedFlatCoefficientBassOverlap.plusFace 15 16 17 r

/-- The negative chart's whole bottom edge selects its own corresponding common-chart nodes. -/
private theorem minus_lower_parameter (r : unitInterval) :
    StdSimplex.map BoundedFlatCoefficientBassOverlap.minusFace.toOrderHom
      (coefficientPausedSquareParameter (r, 0)) =
        binaryPath (k := 35) 33 34 35 r := by
  rw [coefficientPausedSquareParameter_left]
  exact map_binaryPath BoundedFlatCoefficientBassOverlap.minusFace 15 16 17 r


/-- The original positive chart parameter, embedded through the entire retained chart diagram. -/
def plusParameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 45)) :=
  ⟨fun z ↦ StdSimplex.map chartFace.toOrderHom
    (StdSimplex.map BoundedFlatCoefficientBassOverlap.plusFace.toOrderHom
      (BoundedFlatPerfectDoubleSquareScalarPaths.coefficientPausedSquareParameter z)), by fun_prop⟩

/-- The original inverse chart parameter, with its original collapse and pause. -/
def minusParameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 45)) :=
  ⟨fun z ↦ StdSimplex.map chartFace.toOrderHom
    (StdSimplex.map BoundedFlatCoefficientBassOverlap.minusFace.toOrderHom
      (BoundedFlatPerfectDoubleSquareScalarPaths.coefficientPausedSquareParameter z)), by fun_prop⟩

/-- The actual Laurent-composition bottom parameter, using the genuine realization product. -/
def bottomParameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 45)) :=
  ⟨fun z ↦ StdSimplex.map bottomFace.toOrderHom
      (BoundedFlatCoefficientBassLaurentBottomFace.parameter.{u} z),
    by fun_prop⟩

/-- The entire positive shared edge is equal in scalar coordinates. -/
theorem plus_bottom_scalar (r : unitInterval) :
    plusParameter (r, 0) = bottomParameter.{u} (r, 0) := by
  change StdSimplex.map chartFace.toOrderHom
    (StdSimplex.map BoundedFlatCoefficientBassOverlap.plusFace.toOrderHom
      (BoundedFlatPerfectDoubleSquareScalarPaths.coefficientPausedSquareParameter (r, 0))) =
    StdSimplex.map bottomFace.toOrderHom
      (BoundedFlatCoefficientBassLaurentBottomFace.parameter (r, 0))
  rw [plus_lower_parameter, bottom_parameter_left]
  trans binaryPath (k := 44) 21 22 23 r
  · exact map_binaryPath chartFace 15 16 17 r
  · exact (map_binaryPath bottomFace 6 7 8 r).symm

/-- Equality of the separate inverse shared edge, retaining its complete original path. -/
theorem minus_bottom_scalar (r : unitInterval) :
    minusParameter (r, 0) = bottomParameter.{u} (r, 1) := by
  change StdSimplex.map chartFace.toOrderHom
    (StdSimplex.map BoundedFlatCoefficientBassOverlap.minusFace.toOrderHom
      (BoundedFlatPerfectDoubleSquareScalarPaths.coefficientPausedSquareParameter (r, 0))) =
    StdSimplex.map bottomFace.toOrderHom
      (BoundedFlatCoefficientBassLaurentBottomFace.parameter (r, 1))
  rw [minus_lower_parameter, bottom_parameter_right]
  trans binaryPath (k := 44) 42 43 44 r
  · exact map_binaryPath chartFace 33 34 35 r
  · exact (map_binaryPath bottomFace 12 13 14 r).symm

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The complete fixed original positive chart survives the dependent-node merge pointwise. -/
theorem plus_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (W (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n (plusParameter (r, s), x) =
      (boundedAboveFlatCoefficientBassCompositionPlusChart P u v).level n
        (r, (s, (K (polynomialProjection P a)).map n x)) := by
  change prespectrumSimplexFamily (simplex P u v) n
    (StdSimplex.map chartFace.toOrderHom _, x) = _
  rw [prespectrumSimplexFamily_face, chart_face]
  exact BoundedFlatCoefficientBassOverlap.plusChart_native P u v n r s x

/-- The complete fixed original inverse chart survives the same merge pointwise. -/
theorem minus_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (W (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n (minusParameter (r, s), x) =
      (boundedAboveFlatCoefficientBassCompositionMinusChart P u v).level n
        (r, (s, (K (polynomialProjection P a)).map n x)) := by
  change prespectrumSimplexFamily (simplex P u v) n
    (StdSimplex.map chartFace.toOrderHom _, x) = _
  rw [prespectrumSimplexFamily_face, chart_face]
  exact BoundedFlatCoefficientBassOverlap.minusChart_native P u v n r s x

/-- The full prescribed original bottom surface survives, with both times independent. -/
theorem bottom_native (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (W (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n (bottomParameter.{u} (r, t), x) =
      (Homotopy.precomp (boundedAboveFlatCoefficientBassSquareComparison P a)
        (boundedAboveFlatCoefficientLaurentCompositionHomotopy P u v)).level n
        (r, HomotopyPushout.cylinder
          (K (polynomialProjection P a))
          (K (polynomialProjection P a)) n (t, x)) := by
  change prespectrumSimplexFamily (simplex P u v) n
    (StdSimplex.map bottomFace.toOrderHom _, x) = _
  rw [prespectrumSimplexFamily_face, bottom_face]
  exact BoundedFlatCoefficientBassLaurentBottomFace.native P u v n r t x

/-- The merged family fixes the original point for every scalar parameter. -/
theorem family_point (n : ℕ) (z : StdSimplex ℝ (Fin 45)) :
    prespectrumSimplexFamily (simplex P u v) n
      (z, (originalPrespectrum (W (space (op P, a)))).point n) =
      (originalPrespectrum (W
        (space (op P, (laurentUnderFunctor R).obj c)))).point n :=
  prespectrumSimplexFamily_point (simplex P u v) n z

/-- The native structure parameter remains independent of the entire merged scalar family. -/
theorem family_structure (n : ℕ) (z : StdSimplex ℝ (Fin 45))
    (x : (originalPrespectrum (W (space (op P, a)))).space n)
    (t : unitInterval) :
    prespectrumSimplexFamily (simplex P u v) (n + 1)
      (z, (originalPrespectrum
        (W (space (op P, a)))).structureMap n x t) =
    (originalPrespectrum (W
      (space (op P, (laurentUnderFunctor R).obj c)))).structureMap n
        (prespectrumSimplexFamily (simplex P u v) n (z, x)) t :=
  prespectrumSimplexFamily_structure (simplex P u v) n z x t

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassReferenceMerge
