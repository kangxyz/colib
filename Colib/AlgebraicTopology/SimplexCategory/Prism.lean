/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.ToMkOne
public import Colib.Util.References

/-!
# Native ordinal maps for the simplex prism

Mathlib's `SimplexCategory.toMk₁` is the canonical monotone map to the
one-simplex. The prism uses `toMk₁ i.castSucc.succ`, which takes the value zero
at the first `i + 1` vertices. These are consequences of the native face and
degeneracy formulas, not a second definition of the cut map.

The identities adapt `Motivic/Aglib/Algebra/Homology/SingularComplex/Prism.lean`
at revision a6805c4a87cdfd7717dd7a94039246a167f15380. They supply the ordinal
part of MVW2006, Definition 2.17 and the proof of Lemma 2.18, printed pp. 17-18.
-/

@[expose] public section

open CategoryTheory
open scoped Simplicial

namespace SimplexCategory

/-- The first face of the first prism simplex lands at vertex one. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/Algebra/Homology/SingularComplex/Prism.lean:34-38"
  "adaptation" "The first prism endpoint using the native ordinal map to the interval"]
theorem δ_zero_comp_toMk₁_prism (n : ℕ) :
    δ (0 : Fin (n + 2)) ≫ toMk₁ (0 : Fin (n + 1)).castSucc.succ =
      const ⦋n⦌ ⦋1⦌ 1 := by
  rw [δ_comp_toMk₁_of_lt _ _ (by simp)]
  ext j
  simp [toMk₁, const]

/-- The last face of the last prism simplex lands at vertex zero. -/
theorem δ_last_comp_toMk₁_prism (n : ℕ) :
    δ (Fin.last (n + 1)) ≫ toMk₁ (Fin.last n).castSucc.succ =
      const ⦋n⦌ ⦋1⦌ 0 := by
  rw [δ_comp_toMk₁_of_le _ _ (by simp [Fin.le_def])]
  ext j
  simp [toMk₁, const, Fin.lt_def]

/-- Faces before the cut agree with the preceding-dimensional prism. -/
theorem δ_castSucc_comp_toMk₁_prism {n : ℕ} (i : Fin (n + 2))
    (j : Fin (n + 1)) (hij : i ≤ j.castSucc) :
    δ i.castSucc ≫ toMk₁ j.succ.castSucc.succ = toMk₁ j.castSucc.succ := by
  rw [δ_comp_toMk₁_of_lt _ _ (by
    change (i : ℕ) < (j : ℕ) + 1 + 1
    exact Nat.lt_succ_of_le (Nat.le_succ_of_le hij))]
  rfl

/-- The common middle face cancels between consecutive prism simplices. -/
theorem δ_middle_comp_toMk₁_prism {n : ℕ} (j : Fin (n + 1)) :
    δ j.castSucc.succ ≫ toMk₁ j.succ.castSucc.succ =
      δ j.castSucc.succ ≫ toMk₁ j.castSucc.castSucc.succ := by
  rw [δ_comp_toMk₁_of_lt _ _ (by simp [Fin.lt_def]),
    δ_comp_toMk₁_of_le _ _ (by simp)]
  rfl

/-- Faces after the cut agree with the preceding-dimensional prism. -/
theorem δ_succ_comp_toMk₁_prism {n : ℕ} (i : Fin (n + 2))
    (j : Fin (n + 1)) (hji : j.castSucc < i) :
    δ i.succ ≫ toMk₁ j.castSucc.castSucc.succ = toMk₁ j.castSucc.succ := by
  rw [δ_comp_toMk₁_of_le _ _ (by
    change (j : ℕ) + 1 ≤ (i : ℕ) + 1
    exact Nat.succ_le_succ (Nat.le_of_lt hji))]
  rfl

/-- Degeneracies at or before the cut repeat its zero side. -/
theorem σ_castSucc_comp_toMk₁_prism {n : ℕ} (i j : Fin (n + 1)) (hij : i ≤ j) :
    σ i.castSucc ≫ toMk₁ j.castSucc.succ = toMk₁ j.succ.castSucc.succ := by
  rw [σ_comp_toMk₁_of_lt _ _ (by simpa [Fin.lt_def] using Nat.lt_succ_of_le hij)]
  rfl

/-- Degeneracies after the cut repeat its one side. -/
theorem σ_succ_comp_toMk₁_prism {n : ℕ} (i j : Fin (n + 1)) (hji : j ≤ i) :
    σ i.succ ≫ toMk₁ j.castSucc.succ = toMk₁ j.castSucc.castSucc.succ := by
  rw [σ_comp_toMk₁_of_le _ _ (by
    change (j : ℕ) + 1 ≤ (i : ℕ) + 1
    exact Nat.succ_le_succ hji)]
  rfl

end SimplexCategory
