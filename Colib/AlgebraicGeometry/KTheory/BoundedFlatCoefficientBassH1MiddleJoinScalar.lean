/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassH0Native
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassH1MiddleJoinFace
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumSquareFivePath
public import Colib.Topology.Homotopy.OpenCover.TransParameters

/-!
# Exact scalar parameter of the common first and middle Bass H₁ boundary

Both original components use the same five-vertex path with its original
speed, at the target middle quarter on the first component and on the whole
source edge of the middle component. This identifies the scalar evaluations
without assuming a half-cell evaluation for the raw cone homotopy.

Adapted from `BassH0ScalarEdges.lean`, `H1MiddleJoinFace.lean` and
`Quillen/Topology/Path/SimplexCollapsedEdges.lean` in the original proof at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Opposite Convexity Topology Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open FundamentalGroupoid.OpenCover
open scoped Simplicial Topology unitInterval

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH1Join

open BoundedFlatPerfectProjectionRectangleParameters

private theorem collapsed_zero_eval {k : ℕ} {a₀ b₀ : StdSimplex ℝ (Fin (k + 1))}
    {p q : Path a₀ b₀} (J : p.Homotopy q) (t : unitInterval) :
    collapsed J (0, t) = p t := by
  rw [← ThreeSideSquare.collapse_zero t, collapsed_collapse, J.apply_zero]
  rfl

/-- The exact middle quarter gives the whole target path at its native speed. -/
theorem collapsed_top_eval {k : ℕ} {a₀ b₀ a₁ b₁ : StdSimplex ℝ (Fin (k + 1))}
    {p : Path a₀ b₀} {l : Path a₀ a₁} {q : Path a₁ b₁} {m : Path b₀ b₁}
    (J : p.Homotopy ((l.trans q).trans m.symm)) (t : unitInterval) :
    collapsed J (1, t) = q t := by
  rw [← ThreeSideSquare.collapse_topTime t, collapsed_collapse, J.apply_one]
  change ((l.trans q).trans m.symm) (ThreeSideSquare.topTime t) = q t
  rw [← Path.extend_apply ((l.trans q).trans m.symm) (ThreeSideSquare.topTime t).property]
  rw [Path.extend_trans_of_le_half _ _ (by
    dsimp [ThreeSideSquare.topTime]
    linarith [t.2.2])]
  rw [Path.extend_trans_of_half_le _ _ (by
    dsimp [ThreeSideSquare.topTime]
    linarith [t.2.1])]
  have he : 2 * (2 * (ThreeSideSquare.topTime t : ℝ)) - 1 = (t : ℝ) := by
    dsimp [ThreeSideSquare.topTime]
    ring
  rw [he, Path.extend_apply _ t.property]

open BoundedFlatCoefficientBassH0Diagram in
/-- The source edge follows both original signed source paths at their native speed. -/
theorem h0_parameter_zero (t : unitInterval) :
    parameter (0, t) = ((D plusFace).symm.trans (D minusFace)) t :=
  collapsed_zero_eval boundaryParameter t

open BoundedFlatCoefficientBassH0Diagram in
/-- The top edge retains both original polynomial square paths and both signed target paths. -/
theorem h0_parameter_one (t : unitInterval) :
    parameter (1, t) =
      ((Ppath plusFace).trans (((K plusFace).symm.trans (K minusFace)).trans
        (Ppath minusFace).symm)) t :=
  collapsed_top_eval boundaryParameter t

private theorem map_two_binary {k : ℕ} (α : ⦋4⦌ ⟶ ⦋k⦌) (t : unitInterval) :
    embed α (BoundedFlatPerfectNativeSquareFiveSimplex.parameter t) =
      ((binaryPath (α.toOrderHom 0) (α.toOrderHom 1) (α.toOrderHom 2)).symm.trans
        (binaryPath (α.toOrderHom 0) (α.toOrderHom 3) (α.toOrderHom 4))) t :=
  map_trans_values (embed α) _ _ _ _
    (fun r ↦ map_binaryPath α 0 1 2 (unitInterval.symm r)) (map_binaryPath α 0 3 4) t

/-- The first component induces the original middle quarter of its top-edge parameter. -/
theorem first_middle_parameter (t : unitInterval) :
    StdSimplex.map firstMiddleFace.toOrderHom
      (BoundedFlatPerfectNativeSquareFiveSimplex.parameter t) =
      BoundedFlatCoefficientBassH0Diagram.parameter (1, rightHalf (leftHalf t)) := by
  rw [h0_parameter_one, trans_rightHalf, trans_leftHalf]
  exact map_two_binary firstMiddleFace t

/-- The middle component induces its exact original source-edge parameter. -/
theorem middle_source_parameter (t : unitInterval) :
    StdSimplex.map middleSourceFace.toOrderHom
      (BoundedFlatPerfectNativeSquareFiveSimplex.parameter t) =
      BoundedFlatCoefficientBassH0Diagram.parameter (0, t) := by
  rw [h0_parameter_zero]
  exact map_two_binary middleSourceFace t

local notation "W" => BoundedFlatPerfectTripleSimplex.structureOn

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The two actual evaluations coincide on the entire common scalar boundary, in every level. -/
theorem middle_boundary_scalar (n : ℕ) (t : unitInterval)
    (x : (originalPrespectrum (W (space (op P, a)))).space n) :
    prespectrumSimplexFamily (BoundedFlatCoefficientBassH1Components.firstSimplex P u v) n
      (BoundedFlatCoefficientBassH0Diagram.parameter (1, rightHalf (leftHalf t)), x) =
    prespectrumSimplexFamily (BoundedFlatCoefficientBassH1Components.middleSimplex P u v) n
      (BoundedFlatCoefficientBassH0Diagram.parameter (0, t), x) := by
  rw [← first_middle_parameter t, ← middle_source_parameter t]
  let z := BoundedFlatPerfectNativeSquareFiveSimplex.parameter t
  let y : (prespectrum (asSmallCategory (W (space (op P, a))))).space n := x
  have firstEval := prespectrumSimplexFamily_face
    (BoundedFlatCoefficientBassH1Components.firstSimplex P u v) firstMiddleFace n z y
  have middleEval := prespectrumSimplexFamily_face
    (BoundedFlatCoefficientBassH1Components.middleSimplex P u v) middleSourceFace n z y
  have faceEval := congrArg (fun S ↦ prespectrumSimplexFamily S n (z, y)) (middle_face P u v)
  exact firstEval.trans (faceEval.trans middleEval.symm)

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH1Join
