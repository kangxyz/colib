/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassChartBottomReferenceSteps

/-!
# The original merged Bass chart-bottom 44-simplex

The chosen order is the source's exact 45-vertex order. The six shared
vertices are identified only via equality of their complete reference nodes.
Both the chart and Laurent bottom faces retain the original diagrams.
Adapted from `BassMergedBoundarySimplex.lean` in Quillen at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients CommRingCat.PolynomialLaurent
open CategoryTheory.Waldhausen.IteratedS
open scoped Simplicial

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassReferenceMerge

open BoundedFlatCoefficientBassChartBottomReferences

local notation "W" => BoundedFlatPerfectTripleSimplex.structureOn

/-- Original 51-slot representatives in a common order preserving all three full face orders. -/
def select (i : Fin 45) : Fin 51 :=
  ⟨if i.val < 15 then i.val else
    if i.val < 21 then i.val + 21 else
      if i.val < 39 then i.val - 6 else
        if i.val < 42 then i.val + 6 else i.val - 9, by
    split_ifs <;> omega⟩

/-- The vertex map placing the 36 chart vertices in the merged 45-vertex order. -/
def chartIndex (i : Fin 36) : Fin 45 :=
  ⟨if i.val < 15 then i.val else if i.val < 33 then i.val + 6 else i.val + 9, by
    split_ifs <;> omega⟩

/-- The vertex map placing the 15 bottom vertices in the merged 45-vertex order. -/
def bottomIndex (i : Fin 15) : Fin 45 :=
  ⟨if i.val < 9 then i.val + 15 else i.val + 30, by split_ifs <;> omega⟩

/-- The face inclusion retaining the complete chart diagram in the merged boundary simplex. -/
def chartFace : ⦋35⦌ ⟶ ⦋44⦌ := SimplexCategory.Hom.mk ⟨chartIndex, by
  intro i j hij
  change (chartIndex i).val ≤ (chartIndex j).val
  dsimp [chartIndex]
  split_ifs <;> omega⟩

/-- The face inclusion retaining the complete bottom diagram in the merged boundary simplex. -/
def bottomFace : ⦋14⦌ ⟶ ⦋44⦌ := SimplexCategory.Hom.mk ⟨bottomIndex, by
  intro i j hij
  change (bottomIndex i).val ≤ (bottomIndex j).val
  dsimp [bottomIndex]
  split_ifs <;> omega⟩

/-- The fixed chart order recovers each original chart representative. -/
theorem select_chartIndex (i : Fin 36) : select (chartIndex i) = Fin.castAdd 15 i := by
  apply Fin.ext
  dsimp [select, chartIndex]
  split_ifs <;> omega

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- Representatives retain the complete previously frozen reference nodes. -/
def nodes (i : Fin 45) : BoundedFlatCoefficientBassOverlap.Node P u v :=
  BoundedFlatCoefficientBassBottomCommonFamily.nodes P u v (select i)

/-- All six shared full nodes are now identified in one actual 44-simplex. -/
def simplex : ModelSimplex
    (asSmallCategory (W (space (op P, a))))
    (asSmallCategory (W
      (space (op P, (laurentUnderFunctor R).obj c)))) 44 :=
  ModelSimplex.ofIsos (BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (fun i ↦ (nodes P u v i).1) (fun i ↦ (nodes P u v i).2)

/-- Each chart node retains its entire original reference pair. -/
theorem chart_nodes (i : Fin 36) : nodes P u v (chartFace.toOrderHom i) =
    BoundedFlatCoefficientBassBottomCommonFamily.nodes P u v
      (BoundedFlatCoefficientBassBottomCommonFamily.chartFace.toOrderHom i) := by
  unfold nodes
  exact congrArg (BoundedFlatCoefficientBassBottomCommonFamily.nodes P u v) (select_chartIndex i)

/-- Every bottom node is its original full dependent node, including the six shared ones. -/
theorem bottom_nodes (i : Fin 15) : nodes P u v (bottomFace.toOrderHom i) =
    BoundedFlatCoefficientBassBottomCommonFamily.nodes P u v
      (BoundedFlatCoefficientBassBottomCommonFamily.bottomFace.toOrderHom i) := by
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact plus_source_node P u v
  · exact plus_intermediate_node P u v
  · exact plus_target_node P u v
  · rfl
  · rfl
  · rfl
  · exact minus_source_node P u v
  · exact minus_intermediate_node P u v
  · exact minus_target_node P u v

/-- Both whole fixed chart diagrams remain the original precomposed common-chart simplex. -/
theorem chart_face : (simplex P u v).face chartFace =
    BoundedFlatCoefficientBassOverlap.simplex P u v := by
  rw [← BoundedFlatCoefficientBassBottomCommonFamily.chart_face P u v]
  unfold simplex BoundedFlatCoefficientBassBottomCommonFamily.simplex
  rw [ModelSimplex.ofIsos_face, ModelSimplex.ofIsos_face]
  exact ModelSimplex.ofIsos_nodes_congr _ _ (chart_nodes P u v)

/-- The whole bottom grid diagram remains the original one, with all internal transformations. -/
theorem bottom_face : (simplex P u v).face bottomFace =
    BoundedFlatCoefficientBassLaurentBottomFace.simplex P u v := by
  rw [← BoundedFlatCoefficientBassBottomCommonFamily.bottom_face P u v]
  unfold simplex BoundedFlatCoefficientBassBottomCommonFamily.simplex
  rw [ModelSimplex.ofIsos_face, ModelSimplex.ofIsos_face]
  exact ModelSimplex.ofIsos_nodes_congr _ _ (bottom_nodes P u v)

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassReferenceMerge
