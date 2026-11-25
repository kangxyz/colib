/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassUnitTopChartJoins
import Mathlib.Tactic.FinCases

/-! The original 25-node top family of the raw Bass identity, recovering each of
the two actual signed unit charts and the full middle product along their
proved ordinary ordered faces. Adapted from `CoefficientPolynomialSpanUnitTop.lean`
at Quillen `c561118b7795eb9780be9ed391c3251d6a4d0afd`. No native top scalar paste is asserted. -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Opposite CategoryTheory.Waldhausen.IteratedS
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open scoped Simplicial

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassUnitTop

open BoundedFlatCoefficientBassUnitTopCharts

local notation "W" => BoundedFlatPerfectTripleSimplex.structureOn
local notation "bottomSrc" => BoundedFlatCoefficientBassUnitBottom.source
local notation "unitMiddleNodes" => BoundedFlatCoefficientBassUnitTopMiddle.nodes
local notation "unitMiddleSimplex" => BoundedFlatCoefficientBassUnitTopMiddle.simplex

variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)

/-- Five free nodes on each chart, followed by the full original fifteen-node middle grid. -/
def nodes (i : Fin 25) : Node P a :=
  if h : i.val < 5 then plusNodes P a ⟨i.val, by omega⟩ else
    if h' : i.val < 10 then minusNodes P a ⟨i.val - 5, by omega⟩ else
      unitMiddleNodes P a ⟨i.val - 10, by omega⟩

/-- The eight plus-chart node indices in the merged 25-node simplex. -/
def plusIndex (i : Fin 8) : Fin 25 :=
  ⟨if i.val < 5 then i.val else 5 * (i.val - 5) + 12, by split_ifs <;> omega⟩
/-- The eight minus-chart node indices in the merged 25-node simplex. -/
def minusIndex (i : Fin 8) : Fin 25 :=
  ⟨if i.val < 5 then i.val + 5 else 5 * (i.val - 5) + 14, by split_ifs <;> omega⟩
/-- The fifteen middle-grid node indices in the merged 25-node simplex. -/
def middleIndex (i : Fin 15) : Fin 25 := ⟨10 + i.val, by omega⟩

/-- The monotone face selecting the eight plus-chart nodes. -/
def plusFace : ⦋7⦌ ⟶ ⦋24⦌ := SimplexCategory.Hom.mk ⟨plusIndex, by
  intro i j h
  change (plusIndex i).val ≤ (plusIndex j).val
  dsimp [plusIndex]
  split_ifs <;> omega⟩
/-- The monotone face selecting the eight minus-chart nodes. -/
def minusFace : ⦋7⦌ ⟶ ⦋24⦌ := SimplexCategory.Hom.mk ⟨minusIndex, by
  intro i j h
  change (minusIndex i).val ≤ (minusIndex j).val
  dsimp [minusIndex]
  split_ifs <;> omega⟩
/-- The monotone face selecting the fifteen middle-grid nodes. -/
def middleFace : ⦋14⦌ ⟶ ⦋24⦌ := SimplexCategory.Hom.mk ⟨middleIndex, by
  intro i j h
  change 10 + i.val ≤ 10 + j.val
  omega⟩

theorem plus_nodes (i : Fin 8) : nodes P a (plusFace.toOrderHom i) = plusNodes P a i := by
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (plus_shared P a 0).symm
  · exact (plus_shared P a 1).symm
  · exact (plus_shared P a 2).symm

theorem minus_nodes (i : Fin 8) : nodes P a (minusFace.toOrderHom i) = minusNodes P a i := by
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (minus_shared P a 0).symm
  · exact (minus_shared P a 1).symm
  · exact (minus_shared P a 2).symm

theorem middle_nodes (i : Fin 15) :
    nodes P a (middleFace.toOrderHom i) = unitMiddleNodes P a i := by
  fin_cases i <;> rfl

/-- One actual simplex contains all three unchanged moving pieces, with the six joins shared. -/
def simplex : ModelSimplex (asSmallCategory (W (space (op P, a))))
    (asSmallCategory (W
      (space (op P, (laurentUnderFunctor R).obj a)))) 24 :=
  ModelSimplex.ofIsos (bottomSrc P a) (fun i ↦ (nodes P a i).1) (fun i ↦ (nodes P a i).2)

theorem plus_face : (simplex P a).face plusFace =
    BoundedFlatCoefficientBassUnitTopCharts.plusSimplex P a := by
  unfold simplex
  rw [ModelSimplex.ofIsos_face]
  exact ModelSimplex.ofIsos_nodes_congr _ _ (plus_nodes P a)

theorem minus_face : (simplex P a).face minusFace =
    BoundedFlatCoefficientBassUnitTopCharts.minusSimplex P a := by
  unfold simplex
  rw [ModelSimplex.ofIsos_face]
  exact ModelSimplex.ofIsos_nodes_congr _ _ (minus_nodes P a)

theorem middle_face : (simplex P a).face middleFace =
    unitMiddleSimplex P a := by
  unfold simplex
  rw [ModelSimplex.ofIsos_face]
  exact ModelSimplex.ofIsos_nodes_congr _ _ (middle_nodes P a)

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassUnitTop
