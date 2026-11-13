/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Fin.Rev
public import Mathlib.Tactic.FinCases

/-! # The four coordinate expressions for the diagonal determinant

With the chosen nonvanishing coordinate in each factor normalized to `1`, the determinant
of the two coordinate pairs gives the equation `y - x` or `x - y` on the matching charts,
and `1 - xy` or `xy - 1` on the two mixed charts.
-/

@[expose] public section

namespace AlgebraicGeometry.Scheme

variable {R : Type*} [CommRing R]

/-- The two homogeneous coordinates, normalized in the chart indexed by `a`. -/
def projectiveLineChartCoordinatePair (a : Fin 2) (x : R) (i : Fin 2) : R :=
  if i = a then 1 else x

/-- The determinant in the local frames of the two chosen standard charts. -/
def projectiveLineChartDeterminant (a b : Fin 2) (x y : R) : R :=
  projectiveLineChartCoordinatePair a x 0 * projectiveLineChartCoordinatePair b y 1 -
    projectiveLineChartCoordinatePair a x 1 * projectiveLineChartCoordinatePair b y 0

theorem projectiveLineChartDeterminant_same_eq_zero_iff (a : Fin 2) (x y : R) :
    projectiveLineChartDeterminant a a x y = 0 ↔ x = y := by
  fin_cases a <;>
    simp [projectiveLineChartDeterminant, projectiveLineChartCoordinatePair, sub_eq_zero, eq_comm]

theorem projectiveLineChartDeterminant_mixed_eq_zero_iff (a : Fin 2) (x y : R) :
    projectiveLineChartDeterminant a a.rev x y = 0 ↔ x * y = 1 := by
  fin_cases a <;>
    simp [projectiveLineChartDeterminant, projectiveLineChartCoordinatePair, sub_eq_zero,
      eq_comm (a := (1 : R))]

/-- In a mixed chart, the determinant relation forces both affine coordinates to be units. -/
theorem projectiveLineChartDeterminant_isUnit_of_mixed {a : Fin 2} {x y : R}
    (h : projectiveLineChartDeterminant a a.rev x y = 0) : IsUnit x ∧ IsUnit y := by
  have hxy := (projectiveLineChartDeterminant_mixed_eq_zero_iff a x y).mp h
  exact ⟨isUnit_iff_exists_inv.mpr ⟨y, hxy⟩,
    isUnit_iff_exists_inv.mpr ⟨x, by rw [mul_comm, hxy]⟩⟩

end AlgebraicGeometry.Scheme
