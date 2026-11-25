/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases

/-! Representatives of the 63-slot support order of the original Bass boundary calculation.
The scalar indexing itself does not assert any equalities of geometric reference nodes.
Adapted from `BassSupportOrder.lean` and `BassH0MergeIndex.lean` in Quillen,
commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/

@[expose] public section

set_option autoImplicit false

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH0Merged

/-- Scalar reindexing of the old 45 slots; monotonicity is required only on actual supports. -/
def oldIndex : Fin 45 → Fin 63 := ![
    21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35,
    16, 17, 18, 19, 36, 37, 38, 39, 40, 43, 44, 45, 46, 47, 48,
    49, 50, 51, 52, 53, 54, 55, 56, 57, 41, 58, 59, 60, 61, 62]

/-- Scalar reindexing of H0's 31 slots, retaining the thirteen specified shared edge labels. -/
def h0Index : Fin 31 → Fin 63 := ![
    0, 1, 16, 19, 2, 3, 4, 5, 20, 21, 35, 38, 22, 23, 41,
    6, 7, 8, 9, 42, 43, 57, 60, 44, 45, 10, 11, 12, 13, 14,
    15]

/-- All thirteen paired scalar labels agree literally. This does not identify their references. -/
theorem paired_indices (i : Fin 13) :
    h0Index (![2, 3, 9, 10, 11, 12, 13, 14, 20, 21, 22, 23, 24] i) =
      oldIndex (![15, 18, 0, 14, 21, 1, 2, 39, 24, 38, 42, 25, 26] i) := by
  fin_cases i <;> rfl

/-- The finite ordered support representatives retain every original slot. -/
def select (i : Fin 63) : Fin 45 ⊕ Fin 31 :=
  if h₀ : i.val < 2 then .inr ⟨i.val, by omega⟩ else
  if h₁ : i.val < 6 then .inr ⟨i.val + 2, by omega⟩ else
  if h₂ : i.val < 10 then .inr ⟨i.val + 9, by omega⟩ else
  if h₃ : i.val < 16 then .inr ⟨i.val + 15, by omega⟩ else
  if h₄ : i.val < 20 then .inl ⟨i.val - 1, by omega⟩ else
  if h₅ : i.val = 20 then .inr 8 else
  if h₆ : i.val < 36 then .inl ⟨i.val - 21, by omega⟩ else
  if h₇ : i.val < 41 then .inl ⟨i.val - 17, by omega⟩ else
  if h₈ : i.val = 41 then .inl 39 else
  if h₉ : i.val = 42 then .inr 19 else
  if h₁₀ : i.val < 58 then .inl ⟨i.val - 19, by omega⟩ else
    .inl ⟨i.val - 18, by omega⟩

/-- Thirteen shared indices select old representatives; other H₀ slots stay separate. -/
def h0Representative (i : Fin 31) : Fin 45 ⊕ Fin 31 :=
  match i.val with
  | 2 => .inl 15
  | 3 => .inl 18
  | 9 => .inl 0
  | 10 => .inl 14
  | 11 => .inl 21
  | 12 => .inl 1
  | 13 => .inl 2
  | 14 => .inl 39
  | 20 => .inl 24
  | 21 => .inl 38
  | 22 => .inl 42
  | 23 => .inl 25
  | 24 => .inl 26
  | _ => .inr i

theorem select_old (i : Fin 45) : select (oldIndex i) = .inl i := by
  fin_cases i <;> rfl

theorem select_h0 (i : Fin 31) :
    select (h0Index i) = h0Representative i := by
  fin_cases i <;> rfl

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH0Merged
