/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassH0MergedNative
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassH1MiddleJoinScalar

/-!
# Boundary identities in the common Bass 62-simplex

The three H₀ scalar edges agree with their prescribed adjacent faces at
each point; the two chart/bottom identities from the same reindexing are
already established in the primitive support module. The H₀ top evaluates
to the fixed original polynomial composition face. Adapted from
`BassH0TopNativeEdge.lean`, `BassReindexedScalarEdges.lean`, and
`BassH0MergedBoundary.lean` at Quillen commit
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

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH0Merged

open BoundedFlatPerfectProjectionRectangleParameters

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
  change ((l.trans q).trans m.symm) (ThreeSideSquare.leftTime r) = l r
  exact (congrArg (fun t ↦ ((l.trans q).trans m.symm) t) h).trans
    ((trans_leftHalf (l.trans q) m.symm (leftHalf r)).trans (trans_leftHalf l q r))

/-- The original final half retains the inverse boundary path as the native right edge. -/
private theorem collapsed_right_path {k : ℕ} {a₀ b₀ a₁ b₁ : StdSimplex ℝ (Fin (k + 1))}
    {p : Path a₀ b₀} {l : Path a₀ a₁} {q : Path a₁ b₁} {m : Path b₀ b₁}
    (J : p.Homotopy ((l.trans q).trans m.symm)) (r : unitInterval) :
    collapsed J (r, 1) = m r := by
  rw [← ThreeSideSquare.collapse_rightTime r, collapsed_collapse, J.apply_one]
  change ((l.trans q).trans m.symm) (ThreeSideSquare.rightTime r) = m r
  have h : ThreeSideSquare.rightTime r = rightHalf (unitInterval.symm r) := by
    apply Subtype.ext
    rw [coe_rightHalf]
    change 1 - (r : ℝ) / 2 = (1 + (1 - (r : ℝ))) / 2
    ring
  calc
    _ = ((l.trans q).trans m.symm) (rightHalf (unitInterval.symm r)) :=
      congrArg (fun t ↦ ((l.trans q).trans m.symm) t) h
    _ = m.symm (unitInterval.symm r) := trans_rightHalf (l.trans q) m.symm _
    _ = m r := by
      change m (unitInterval.symm (unitInterval.symm r)) = m r
      rw [unitInterval.symm_symm]

/-- The native H₀ square has its original entire positive projection edge. -/
theorem h0_parameter_left (s : unitInterval) :
    BoundedFlatCoefficientBassH0Diagram.parameter (s, 0) =
      L BoundedFlatCoefficientBassH0Diagram.plusFace s :=
  collapsed_left_path BoundedFlatCoefficientBassH0Diagram.boundaryParameter s

/-- The native H₀ square has its original entire inverse projection edge. -/
theorem h0_parameter_right (s : unitInterval) :
    BoundedFlatCoefficientBassH0Diagram.parameter (s, 1) =
      L BoundedFlatCoefficientBassH0Diagram.minusFace s :=
  collapsed_right_path BoundedFlatCoefficientBassH0Diagram.boundaryParameter s

/-- Affine relabeling preserves an original edge without needing a global order. -/
private theorem map_any_edge {k l : ℕ} (f : Fin (k + 1) → Fin (l + 1))
    (i j : Fin (k + 1)) (t : unitInterval) :
    StdSimplex.map f (edge i j t) = edge (f i) (f j) t :=
  StdSimplex.map_duple (unitInterval.nonneg (unitInterval.symm t))
    (unitInterval.nonneg t) (by simp) i j f

/-- Both original half-speed normalization segments are retained by any affine relabeling. -/
theorem map_any_binary {k l : ℕ} (f : Fin (k + 1) → Fin (l + 1))
    (i j m : Fin (k + 1)) (t : unitInterval) :
    StdSimplex.map f (binaryPath i j m t) = binaryPath (f i) (f j) (f m) t :=
  map_trans_values _ _ _ _ _ (map_any_edge f i j) (map_any_edge f j m) t

/-- The exact reversed-and-concatenated five-node path is preserved with its native speeds. -/
theorem map_two_binary {k l : ℕ} (f : Fin (k + 1) → Fin (l + 1))
    (i j m n p : Fin (k + 1)) (t : unitInterval) :
    StdSimplex.map f (((binaryPath i j m).symm.trans (binaryPath i n p)) t) =
      ((binaryPath (f i) (f j) (f m)).symm.trans (binaryPath (f i) (f n) (f p))) t :=
  map_trans_values _ _ _ _ _ (fun s ↦ map_any_binary f i j m (unitInterval.symm s))
    (map_any_binary f i n p) t

private theorem two_binary_congr {k : ℕ} {i j m n p i' j' m' n' p' : Fin (k + 1)}
    (hi : i = i') (hj : j = j') (hm : m = m') (hn : n = n') (hp : p = p')
    (t : unitInterval) :
    ((binaryPath i j m).symm.trans (binaryPath i n p)) t =
      ((binaryPath i' j' m').symm.trans (binaryPath i' n' p')) t := by
  subst i'
  subst j'
  subst m'
  subst n'
  subst p'
  rfl

/-- The original paused chart starts on the complete outer path without changing its clock. -/
theorem paused_chart_zero (s : unitInterval) :
    BoundedFlatPerfectDoubleSquareScalarPaths.coefficientPausedSquareParameter (0, s) =
      BoundedFlatPerfectDoubleSquareScalarPaths.outerSquarePath s := by
  unfold BoundedFlatPerfectDoubleSquareScalarPaths.coefficientPausedSquareParameter
  rw [← ThreeSideSquare.collapse_zero s, collapsed_collapse,
    (pauseRightParameter
      BoundedFlatPerfectDoubleSquareScalarPaths.coefficientBoundaryParameter).apply_zero]
  rfl

/-- Entire positive H0/chart edge equality, including each original reversal and speed. -/
theorem h0_plus_scalar (s : unitInterval) : h0Parameter (s, 0) = plusParameter (0, s) := by
  change StdSimplex.map h0Index (BoundedFlatCoefficientBassH0Diagram.parameter (s, 0)) =
    StdSimplex.map oldIndex (StdSimplex.map
      BoundedFlatCoefficientBassReferenceMerge.chartFace.toOrderHom
      (StdSimplex.map BoundedFlatCoefficientBassOverlap.plusFace.toOrderHom
        (BoundedFlatPerfectDoubleSquareScalarPaths.coefficientPausedSquareParameter (0, s))))
  rw [h0_parameter_left, paused_chart_zero,
    ← StdSimplex.map_comp, ← StdSimplex.map_comp]
  change StdSimplex.map h0Index
      (((binaryPath (k := 30) 9 10 11).symm.trans (binaryPath 9 12 13)) s) =
    StdSimplex.map _
      (((binaryPath (k := 17) 0 14 15).symm.trans (binaryPath 0 1 2)) s)
  rw [map_two_binary, map_two_binary]
  rfl

/-- Entire inverse H0/chart edge equality, retaining the distinct inverse chart. -/
theorem h0_minus_scalar (s : unitInterval) : h0Parameter (s, 1) = minusParameter (0, s) := by
  change StdSimplex.map h0Index (BoundedFlatCoefficientBassH0Diagram.parameter (s, 1)) =
    StdSimplex.map oldIndex (StdSimplex.map
      BoundedFlatCoefficientBassReferenceMerge.chartFace.toOrderHom
      (StdSimplex.map BoundedFlatCoefficientBassOverlap.minusFace.toOrderHom
        (BoundedFlatPerfectDoubleSquareScalarPaths.coefficientPausedSquareParameter (0, s))))
  rw [h0_parameter_right, paused_chart_zero,
    ← StdSimplex.map_comp, ← StdSimplex.map_comp]
  change StdSimplex.map h0Index
      (((binaryPath (k := 30) 20 21 22).symm.trans (binaryPath 20 23 24)) s) =
    StdSimplex.map _
      (((binaryPath (k := 17) 0 14 15).symm.trans (binaryPath 0 1 2)) s)
  rw [map_two_binary, map_two_binary]
  simp only [Function.comp_apply]
  have h20 : h0Index 20 = oldIndex (BoundedFlatCoefficientBassReferenceMerge.chartFace.toOrderHom
      (BoundedFlatCoefficientBassOverlap.minusFace.toOrderHom 0)) := rfl
  have h21 : h0Index 21 = oldIndex (BoundedFlatCoefficientBassReferenceMerge.chartFace.toOrderHom
      (BoundedFlatCoefficientBassOverlap.minusFace.toOrderHom 14)) := rfl
  have h22 : h0Index 22 = oldIndex (BoundedFlatCoefficientBassReferenceMerge.chartFace.toOrderHom
      (BoundedFlatCoefficientBassOverlap.minusFace.toOrderHom 15)) := rfl
  have h23 : h0Index 23 = oldIndex (BoundedFlatCoefficientBassReferenceMerge.chartFace.toOrderHom
      (BoundedFlatCoefficientBassOverlap.minusFace.toOrderHom 1)) := rfl
  have h24 : h0Index 24 = oldIndex (BoundedFlatCoefficientBassReferenceMerge.chartFace.toOrderHom
      (BoundedFlatCoefficientBassOverlap.minusFace.toOrderHom 2)) := rfl
  exact two_binary_congr h20 h21 h22 h23 h24 s

/-- The source edge of the actual product parameter is its original five-node Bass path. -/
private theorem bottom_zero (t : unitInterval) :
    BoundedFlatCoefficientBassLaurentBottomFace.parameter.{u} (0, t) =
      ((binaryPath (k := 14) 0 3 6).symm.trans (binaryPath 0 9 12)) t := by
  change SimplexGrid.parameter.{u + 1} 4 2
    (BoundedFlatCoefficientBassProjectionPath.parameter t, binaryPath (k := 2) 0 1 2 0) = _
  rw [Path.source, SimplexGrid.parameter_column]
  exact map_two_binary (SimplexGrid.columnFace 4 2 0).toOrderHom 0 1 2 3 4 t

/-- Entire H0/bottom shared edge equality from the actual realized-product column restriction. -/
theorem h0_bottom_scalar (t : unitInterval) :
    h0Parameter (0, t) = bottomParameter.{u} (0, t) := by
  change StdSimplex.map h0Index (BoundedFlatCoefficientBassH0Diagram.parameter (0, t)) =
    StdSimplex.map oldIndex (StdSimplex.map
      BoundedFlatCoefficientBassReferenceMerge.bottomFace.toOrderHom
      (BoundedFlatCoefficientBassLaurentBottomFace.parameter (0, t)))
  rw [BoundedFlatCoefficientBassH1Join.h0_parameter_zero, bottom_zero, ← StdSimplex.map_comp]
  change StdSimplex.map h0Index
      (((binaryPath (k := 30) 2 3 11).symm.trans (binaryPath 2 14 22)) t) =
    StdSimplex.map _
      (((binaryPath (k := 14) 0 3 6).symm.trans (binaryPath 0 9 12)) t)
  rw [map_two_binary, map_two_binary]
  simp only [Function.comp_apply]
  have h2 : h0Index 2 =
    oldIndex (BoundedFlatCoefficientBassReferenceMerge.bottomFace.toOrderHom 0) := rfl
  have h3 : h0Index 3 =
    oldIndex (BoundedFlatCoefficientBassReferenceMerge.bottomFace.toOrderHom 3) := rfl
  have h11 : h0Index 11 =
    oldIndex (BoundedFlatCoefficientBassReferenceMerge.bottomFace.toOrderHom 6) := rfl
  have h14 : h0Index 14 =
    oldIndex (BoundedFlatCoefficientBassReferenceMerge.bottomFace.toOrderHom 9) := rfl
  have h22 : h0Index 22 =
    oldIndex (BoundedFlatCoefficientBassReferenceMerge.bottomFace.toOrderHom 12) := rfl
  exact two_binary_congr h2 h3 h11 h14 h22 t

local notation "W" => BoundedFlatPerfectTripleSimplex.structureOn
local notation "K" => boundedAboveFlatPerfectPullbackPrespectrumMap

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The whole original top edge of H0 agrees with the fixed native M face at r = 0. -/
private theorem top_native_edge (n : ℕ) (t : unitInterval)
    (x : (originalPrespectrum (W (space (op P, a)))).space n) :
    prespectrumSimplexFamily (BoundedFlatCoefficientBassH0Merge.simplex P u v) n
      (BoundedFlatCoefficientBassH0Diagram.parameter (1, t), x) =
      ((boundedAboveFlatCoefficientPolynomialSpanCompositionHomotopy P u v).postcomp
        (boundedAboveFlatCoefficientBassSquareComparison P c)).level n
          (0, HomotopyPushout.cylinder
            (K (polynomialProjection P a))
            (K (polynomialProjection P a)) n (t, x)) := by
  rw [BoundedFlatCoefficientBassH0Merge.simplex_original,
    BoundedFlatCoefficientBassH0Diagram.composition_H0]
  exact ((boundedAboveFlatCoefficientBassComparisonHomotopy P (u ≫ v)).at_one n _).trans
    (((boundedAboveFlatCoefficientPolynomialSpanCompositionHomotopy P u v).postcomp
      (boundedAboveFlatCoefficientBassSquareComparison P c)).at_zero n _).symm

/-- The H₀ top edge in the common simplex is the original native polynomial composition face. -/
theorem h0_top_native (n : ℕ) (t : unitInterval)
    (x : (originalPrespectrum (W (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n (h0Parameter (1, t), x) =
      ((boundedAboveFlatCoefficientPolynomialSpanCompositionHomotopy P u v).postcomp
        (boundedAboveFlatCoefficientBassSquareComparison P c)).level n
          (0, HomotopyPushout.cylinder
            (K (polynomialProjection P a)) (K (polynomialProjection P a)) n (t, x)) :=
  (h0_family P u v n (1, t) x).trans (top_native_edge P u v n t x)

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH0Merged
