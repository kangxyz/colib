/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassH0MergedFaces
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassH0Native
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassMergedScalarBoundary
public import Colib.Topology.Path.Homotopy.ParameterBoundarySupport

/-!
# Primitive support and the signed Bass chart/bottom edges

The three primitive comparisons lie in their original split-triple faces.
Both signed charts retain their respective bottom edges after affine
relabeling. Adapted from `BassPrimitiveSupport.lean`,
`BassReindexedScalarEdges.lean`, and `BassH0MergedBoundary.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd` in Quillen.
-/

@[expose] public noncomputable section

set_option autoImplicit false

open CategoryTheory Convexity Topology
open CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open scoped Simplicial Topology unitInterval

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH0Merged

/-- The subset covered by the three original primitive seven-simplices. -/
def rectangleSupport : Set (StdSimplex ℝ (Fin 18)) :=
  {z | ∃ i : Fin 3, ∃ y : StdSimplex ℝ (Fin 8), embed (rectangleFace i) y = z}

open BoundedFlatPerfectDoubleSquareScalarPaths
open BoundedFlatPerfectSplitTripleParameters

/-- The first primitive comparison retains its complete original face. -/
theorem first_comparison_mem (z : unitInterval × unitInterval) :
    firstComparison z ∈ rectangleSupport :=
  ⟨0, comparisonParameter z, rfl⟩

/-- The middle primitive comparison retains its complete original face. -/
theorem middle_comparison_mem (z : unitInterval × unitInterval) :
    middleComparison z ∈ rectangleSupport :=
  ⟨1, comparisonParameter z, rfl⟩

/-- The last primitive comparison retains its complete original face. -/
theorem last_comparison_mem (z : unitInterval × unitInterval) :
    lastComparison z ∈ rectangleSupport :=
  ⟨2, comparisonParameter z, rfl⟩

open Path.Homotopy.ParameterSupport

/-- The full three-route parameter stays in the same three primitive faces. -/
theorem rectangle_in : HomotopyIn rectangleSupport rectangleParameter :=
  threeRoutes_in first_comparison_mem middle_comparison_mem last_comparison_mem

/-- Reversing the path parameter and transporting endpoints preserve the same support. -/
theorem original_comparison_in : HomotopyIn rectangleSupport originalComparisonParameter :=
  hom_cast (hom_symm₂ rectangle_in) _ _

/-- The original coefficient boundary has no scalar values outside the primitive support. -/
theorem coefficient_boundary_in : HomotopyIn rectangleSupport coefficientBoundaryParameter :=
  boundaryOfComparison_in original_comparison_in

/-- The terminal pause and collapse preserve the same actual support. -/
theorem paused_chart_in (z : unitInterval × unitInterval) :
    coefficientPausedSquareParameter z ∈ rectangleSupport :=
  collapsed_in (pauseRight_in coefficient_boundary_in) z

private theorem embed_comp {i j k : ℕ} (α : ⦋i⦌ ⟶ ⦋j⦌) (β : ⦋j⦌ ⟶ ⦋k⦌)
    (z : StdSimplex ℝ (Fin (i + 1))) : embed β (embed α z) = embed (α ≫ β) z := by
  change StdSimplex.map β.toOrderHom (StdSimplex.map α.toOrderHom z) = _
  rw [← StdSimplex.map_comp]
  rfl

/-- Under an enclosing face, each supported point still factors through the same primitive face. -/
theorem map_supported {k : ℕ} (α : ⦋17⦌ ⟶ ⦋k⦌) {z : StdSimplex ℝ (Fin 18)}
    (hz : z ∈ rectangleSupport) :
    ∃ i : Fin 3, ∃ y : StdSimplex ℝ (Fin 8), embed (rectangleFace i ≫ α) y = embed α z := by
  obtain ⟨i, y, rfl⟩ := hz
  exact ⟨i, y, (embed_comp _ _ _).symm⟩

/-- The positive and inverse charts each contribute exactly their three primitive faces. -/
def h0Support : Set (StdSimplex ℝ (Fin 31)) :=
  (embed BoundedFlatCoefficientBassH0Diagram.plusFace) '' rectangleSupport ∪
    (embed BoundedFlatCoefficientBassH0Diagram.minusFace) '' rectangleSupport

open BoundedFlatPerfectProjectionRectangleParameters

private theorem h0_plus_in :
    HomotopyIn h0Support (rectangle BoundedFlatCoefficientBassH0Diagram.plusFace) :=
  fun z ↦ Or.inl ⟨rectangleParameter z, rectangle_in z, rfl⟩

private theorem h0_minus_in :
    HomotopyIn h0Support (rectangle BoundedFlatCoefficientBassH0Diagram.minusFace) :=
  fun z ↦ Or.inr ⟨rectangleParameter z, rectangle_in z, rfl⟩

/-- The original full projection pasting has support in the six primitive faces. -/
theorem h0_boundary_in :
    HomotopyIn h0Support BoundedFlatCoefficientBassH0Diagram.boundaryParameter :=
  pasteProjectionSquares_in h0_plus_in h0_minus_in

/-- The actual descended H₀ square stays within those same six faces. -/
theorem h0_in (z : unitInterval × unitInterval) :
    BoundedFlatCoefficientBassH0Diagram.parameter z ∈ h0Support :=
  collapsed_in h0_boundary_in z

/-- Every original H₀ value factors explicitly through one of its six primitive faces. -/
theorem h0_support (z : unitInterval × unitInterval) :
    ∃ α ∈ ({BoundedFlatCoefficientBassH0Diagram.plusFace,
      BoundedFlatCoefficientBassH0Diagram.minusFace} :
      Set (⦋17⦌ ⟶ ⦋30⦌)), ∃ i : Fin 3, ∃ y : StdSimplex ℝ (Fin 8),
        embed (rectangleFace i ≫ α) y = BoundedFlatCoefficientBassH0Diagram.parameter z := by
  rcases h0_in z with ⟨w, hw, he⟩ | ⟨w, hw, he⟩
  · obtain ⟨i, y, hy⟩ := map_supported BoundedFlatCoefficientBassH0Diagram.plusFace hw
    exact ⟨_, Set.mem_insert _ _, i, y, hy.trans he⟩
  · obtain ⟨i, y, hy⟩ := map_supported BoundedFlatCoefficientBassH0Diagram.minusFace hw
    exact ⟨_, Set.mem_insert_of_mem _ (Set.mem_singleton _), i, y, hy.trans he⟩

/-- The positive chart parameter relabeled by the original boundary node index. -/
def plusParameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 63)) :=
  ⟨fun z ↦ StdSimplex.map oldIndex (BoundedFlatCoefficientBassReferenceMerge.plusParameter z),
    by fun_prop⟩

/-- The inverse-coordinate chart parameter relabeled by the same boundary node index. -/
def minusParameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 63)) :=
  ⟨fun z ↦ StdSimplex.map oldIndex (BoundedFlatCoefficientBassReferenceMerge.minusParameter z),
    by fun_prop⟩

/-- The original realized-product bottom parameter relabeled using the same index. -/
def bottomParameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 63)) :=
  ⟨fun z ↦ StdSimplex.map oldIndex (BoundedFlatCoefficientBassReferenceMerge.bottomParameter.{u} z),
    by fun_prop⟩

/-- Equality of the entire original positive chart/bottom edge survives relabeling. -/
theorem plus_bottom_scalar (r : unitInterval) :
    plusParameter (r, 0) = bottomParameter.{u} (r, 0) :=
  congrArg (StdSimplex.map oldIndex) (BoundedFlatCoefficientBassReferenceMerge.plus_bottom_scalar r)

/-- Equality of the entire original inverse chart/bottom edge survives relabeling. -/
theorem minus_bottom_scalar (r : unitInterval) :
    minusParameter (r, 0) = bottomParameter.{u} (r, 1) :=
  congrArg (StdSimplex.map oldIndex)
    (BoundedFlatCoefficientBassReferenceMerge.minus_bottom_scalar r)

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH0Merged
