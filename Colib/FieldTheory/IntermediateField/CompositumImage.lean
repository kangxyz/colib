/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic

import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure

/-!
# Compositum with the image of a field

The image of a field in an overfield factors through its compositum with a second
field. Finiteness and pure inseparability pass to this compositum from the
corresponding extensions of a common base.
-/

@[expose] public noncomputable section

namespace IntermediateField

section

variable (A B D : Type*) [Field A] [Field B] [Field D] [Algebra A D] [Algebra B D]

/-- The embedding of `A` into the field generated over `B` by its image in `D`. -/
def adjoinRangeFactor : A →+* adjoin B (Set.range (algebraMap A D)) :=
  (algebraMap A D).codRestrict _ fun a ↦ subset_adjoin B _ ⟨a, rfl⟩

@[simp]
theorem coe_adjoinRangeFactor (a : A) :
    (adjoinRangeFactor A B D a : D) = algebraMap A D a := rfl

/-- The factored image of `A` generates the compositum over `B`. -/
theorem adjoin_range_adjoinRangeFactor_eq_top :
    adjoin B (Set.range (adjoinRangeFactor A B D)) =
      (⊤ : IntermediateField B (adjoin B (Set.range (algebraMap A D)))) := by
  let C := adjoin B (Set.range (algebraMap A D))
  apply map_injective C.val
  rw [adjoin_map, ← Set.range_comp, ← AlgHom.fieldRange_eq_map, fieldRange_val]
  rfl

end

section

variable (K A B D : Type*) [Field K] [Field A] [Field B] [Field D]
  [Algebra K A] [Algebra K B] [Algebra K D] [Algebra A D] [Algebra B D]
  [IsScalarTower K A D] [IsScalarTower K B D]

/-- If `A` is finite over `K`, its compositum with `B` in `D` is finite over `B`. -/
theorem finiteDimensional_adjoin_range_of_finiteDimensional [FiniteDimensional K A] :
    FiniteDimensional B (adjoin B (Set.range (algebraMap A D))) := by
  classical
  obtain ⟨s, hs⟩ := fg_top K A
  let f := IsScalarTower.toAlgHom K A D
  have hrange : (adjoin K (s.image f : Set D) : Set D) = Set.range (algebraMap A D) := by
    change (adjoin K (s.image f : Set D) : Set D) = (f.fieldRange : Set D)
    rw [Finset.coe_image, ← adjoin_map, hs, ← AlgHom.fieldRange_eq_map]
  rw [← hrange, adjoin_adjoin_right]
  apply finiteDimensional_adjoin
  intro z hz
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hz
  have ha : IsIntegral K a := Algebra.IsIntegral.isIntegral a
  exact (ha.map f).tower_top

/-- If `B` is purely inseparable over `K`, the compositum is purely inseparable over
the embedded copy of `A`. -/
theorem isPurelyInseparable_adjoin_range [IsPurelyInseparable K B] :
    letI : Algebra A (adjoin B (Set.range (algebraMap A D))) :=
      (adjoinRangeFactor A B D).toAlgebra
    IsPurelyInseparable A (adjoin B (Set.range (algebraMap A D))) := by
  let C := adjoin B (Set.range (algebraMap A D))
  let : Algebra A C := (adjoinRangeFactor A B D).toAlgebra
  let : IsScalarTower A C D := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  obtain ⟨p, _⟩ := ExpChar.exists K
  let : ExpChar A p := expChar_of_injective_algebraMap (algebraMap K A).injective p
  let P := perfectClosure A D
  have hB (b : B) : algebraMap B D b ∈ P := by
    obtain ⟨n, k, hk⟩ := IsPurelyInseparable.pow_mem K p b
    refine (mem_perfectClosure_iff_pow_mem p).2 ⟨n, algebraMap K A k, ?_⟩
    rw [← IsScalarTower.algebraMap_apply K A D, IsScalarTower.algebraMap_apply K B D,
      hk, map_pow]
  have hC : C ≤ P.toSubfield.toIntermediateField hB := by
    apply adjoin_le_iff.mpr
    rintro _ ⟨a, rfl⟩
    exact P.algebraMap_mem a
  change IsPurelyInseparable A C
  apply (isPurelyInseparable_iff_pow_mem A p).2
  intro x
  have hx : (x : D) ∈ perfectClosure A D := hC x.property
  obtain ⟨n, a, ha⟩ := (mem_perfectClosure_iff_pow_mem p).1 hx
  refine ⟨n, a, (algebraMap C D).injective ?_⟩
  rw [← IsScalarTower.algebraMap_apply A C D, map_pow]
  exact ha

end

end IntermediateField

end
