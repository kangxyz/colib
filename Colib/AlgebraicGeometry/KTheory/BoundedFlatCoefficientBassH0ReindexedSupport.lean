/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassH0PrimitiveSupport

/-!
# Scalar factorizations through the thirteen Bass support faces

Every scalar value of the positive chart, the inverse chart, the realized
bottom product and the H₀ paste lies on an actual retained face of the common
62-simplex. Adapted from `BassReindexedSupport.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

open CategoryTheory Convexity Topology
open CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open scoped Simplicial Topology unitInterval

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH0Merged

/-- The original H₀ parameter relabeled by the exact 63-slot support order. -/
def h0Parameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 63)) :=
  ⟨fun z ↦ StdSimplex.map h0Index (BoundedFlatCoefficientBassH0Diagram.parameter z), by fun_prop⟩

/-- The plus chart is covered by its own three actual retained seven-faces. -/
theorem plus_support (z : unitInterval × unitInterval) :
    ∃ i : Fin 3, ∃ y : StdSimplex ℝ (Fin 8), embed (oldPlusFace i) y = plusParameter z := by
  obtain ⟨i, y, hy⟩ := map_supported
    (BoundedFlatCoefficientBassOverlap.plusFace ≫
      BoundedFlatCoefficientBassReferenceMerge.chartFace)
    (paused_chart_in z)
  refine ⟨i, y, ?_⟩
  have he := congrArg (StdSimplex.map oldIndex) hy
  change StdSimplex.map oldIndex
      (StdSimplex.map (rectangleFace i ≫ (BoundedFlatCoefficientBassOverlap.plusFace ≫
        BoundedFlatCoefficientBassReferenceMerge.chartFace)).toOrderHom y) =
    StdSimplex.map oldIndex (StdSimplex.map
      (BoundedFlatCoefficientBassOverlap.plusFace ≫
        BoundedFlatCoefficientBassReferenceMerge.chartFace).toOrderHom
      (BoundedFlatPerfectDoubleSquareScalarPaths.coefficientPausedSquareParameter z)) at he
  rw [← StdSimplex.map_comp] at he
  refine he.trans ?_
  change StdSimplex.map oldIndex (StdSimplex.map
      (BoundedFlatCoefficientBassReferenceMerge.chartFace.toOrderHom ∘
        BoundedFlatCoefficientBassOverlap.plusFace.toOrderHom)
      (BoundedFlatPerfectDoubleSquareScalarPaths.coefficientPausedSquareParameter z)) =
    plusParameter z
  rw [StdSimplex.map_comp]; rfl

/-- The minus chart is covered by its own three actual retained seven-faces. -/
theorem minus_support (z : unitInterval × unitInterval) :
    ∃ i : Fin 3, ∃ y : StdSimplex ℝ (Fin 8), embed (oldMinusFace i) y = minusParameter z := by
  obtain ⟨i, y, hy⟩ := map_supported
    (BoundedFlatCoefficientBassOverlap.minusFace ≫
      BoundedFlatCoefficientBassReferenceMerge.chartFace)
    (paused_chart_in z)
  refine ⟨i, y, ?_⟩
  have he := congrArg (StdSimplex.map oldIndex) hy
  change StdSimplex.map oldIndex
      (StdSimplex.map (rectangleFace i ≫ (BoundedFlatCoefficientBassOverlap.minusFace ≫
        BoundedFlatCoefficientBassReferenceMerge.chartFace)).toOrderHom y) =
    StdSimplex.map oldIndex (StdSimplex.map
      (BoundedFlatCoefficientBassOverlap.minusFace ≫
        BoundedFlatCoefficientBassReferenceMerge.chartFace).toOrderHom
      (BoundedFlatPerfectDoubleSquareScalarPaths.coefficientPausedSquareParameter z)) at he
  rw [← StdSimplex.map_comp] at he
  refine he.trans ?_
  change StdSimplex.map oldIndex (StdSimplex.map
      (BoundedFlatCoefficientBassReferenceMerge.chartFace.toOrderHom ∘
        BoundedFlatCoefficientBassOverlap.minusFace.toOrderHom)
      (BoundedFlatPerfectDoubleSquareScalarPaths.coefficientPausedSquareParameter z)) =
    minusParameter z
  rw [StdSimplex.map_comp]; rfl

/-- The full realized bottom product factors through the retained fourteen-face. -/
theorem bottom_support (z : unitInterval × unitInterval) :
    ∃ y : StdSimplex ℝ (Fin 15), embed supportedBottomFace y = bottomParameter.{u} z := by
  refine ⟨BoundedFlatCoefficientBassLaurentBottomFace.parameter z, ?_⟩
  change StdSimplex.map
      (oldIndex ∘ BoundedFlatCoefficientBassReferenceMerge.bottomFace.toOrderHom) _ =
    StdSimplex.map oldIndex
      (StdSimplex.map BoundedFlatCoefficientBassReferenceMerge.bottomFace.toOrderHom _)
  rw [StdSimplex.map_comp]

/-- All of the original two-chart H₀ paste factors through the six retained seven-faces. -/
theorem h0_reindexed_support (z : unitInterval × unitInterval) :
    (∃ i : Fin 3, ∃ y : StdSimplex ℝ (Fin 8), embed (h0PlusFace i) y = h0Parameter z) ∨
    (∃ i : Fin 3, ∃ y : StdSimplex ℝ (Fin 8), embed (h0MinusFace i) y = h0Parameter z) := by
  obtain ⟨α, hα, i, y, hy⟩ := h0_support z
  have he := congrArg (StdSimplex.map h0Index) hy
  change StdSimplex.map h0Index (StdSimplex.map (rectangleFace i ≫ α).toOrderHom y) =
    h0Parameter z at he
  rw [← StdSimplex.map_comp] at he
  rcases Set.mem_insert_iff.mp hα with hα | hα
  · subst α
    exact Or.inl ⟨i, y, he⟩
  · have hα' := Set.mem_singleton_iff.mp hα
    subst α
    exact Or.inr ⟨i, y, he⟩

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH0Merged
