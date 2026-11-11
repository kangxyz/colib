/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic

import Colib.FieldTheory.PGroupSeparablePresentation

/-!
# Normal prime subfields inside a normal extension of prime-power degree

In characteristic `p`, the separable subextension of a finite normal extension of `p`-power
degree is Galois with a `p`-group of automorphisms. The separable closure of the embedded
field therefore supplies a normal prime step whenever it is nontrivial. In the purely
inseparable case a least Frobenius power produces an element of degree `p`.
-/

@[expose] public noncomputable section

open Polynomial

namespace IntermediateField

variable {k L Ω : Type*} [Field k] [Field L] [Field Ω]
  [Algebra k L] [Algebra k Ω] [FiniteDimensional k L] [FiniteDimensional k Ω]

private theorem exists_prime_subfield_of_isPurelyInseparable
    (p : ℕ) [Fact p.Prime] [CharP k p] [IsPurelyInseparable k L]
    (hL : 1 < Module.finrank k L) :
    ∃ P : IntermediateField k L, IsPurelyInseparable k P ∧ Module.finrank k P = p := by
  classical
  have hp : p.Prime := Fact.out
  have hbot : (⊥ : IntermediateField k L) ≠ ⊤ := fun h =>
    (Nat.ne_of_gt hL) (bot_eq_top_iff_finrank_eq_one.mp h)
  obtain ⟨x, _, hx⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne bot_le hbot)
  have hpow : ∃ n : ℕ, x ^ (p ^ n) ∈ (⊥ : IntermediateField k L) := by
    obtain ⟨n, a, ha⟩ := IsPurelyInseparable.pow_mem k p x
    exact ⟨n, mem_bot.mpr ⟨a, ha⟩⟩
  have hfind : Nat.find hpow ≠ 0 := fun h =>
    hx (by simpa [h] using Nat.find_spec hpow)
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hfind
  let y : L := x ^ (p ^ m)
  have hy : y ∉ (⊥ : IntermediateField k L) :=
    Nat.find_min hpow (m := m) (by rw [hm]; exact Nat.lt_succ_self m)
  have hypow : y ^ p ∈ (⊥ : IntermediateField k L) := by
    change (x ^ (p ^ m)) ^ p ∈ (⊥ : IntermediateField k L)
    rw [← pow_mul, ← pow_succ]
    simpa only [hm] using Nat.find_spec hpow
  obtain ⟨b, hb⟩ := mem_bot.mp hypow
  have hdvd : minpoly k y ∣ X ^ p - C b := minpoly.dvd k y (by
    rw [map_sub, map_pow, aeval_X, aeval_C, hb, sub_self])
  have hdegree : (X ^ p - C b : k[X]).natDegree = p := by
    rw [natDegree_sub_C, natDegree_X_pow]
  have hle : (minpoly k y).natDegree ≤ p := by
    have hq : (X ^ p - C b : k[X]) ≠ 0 :=
      ne_zero_of_natDegree_gt (by rw [hdegree]; exact hp.pos)
    simpa only [hdegree] using natDegree_le_of_dvd hdvd hq
  obtain ⟨e, a, he⟩ := IsPurelyInseparable.minpoly_eq_X_pow_sub_C k p y
  have hdegreePow : (minpoly k y).natDegree = p ^ e := by
    rw [he, natDegree_sub_C, natDegree_X_pow]
  have he0 : e ≠ 0 := fun h => hy (mem_bot.mpr (minpoly.natDegree_eq_one_iff.mp (by
    simpa [h] using hdegreePow)))
  have hge : p ≤ (minpoly k y).natDegree := by
    rw [hdegreePow]
    simpa only [pow_one] using Nat.pow_le_pow_right hp.pos (Nat.one_le_iff_ne_zero.mpr he0)
  refine ⟨k⟮y⟯, inferInstance, ?_⟩
  rw [adjoin.finrank (IsIntegral.of_finite k y)]
  exact le_antisymm hle hge

/-- A nontrivial finite extension embedded in a finite normal extension of characteristic `p`
and `p`-power degree contains an actual normal degree-`p` subfield. -/
theorem exists_normal_prime_subfield_of_finrank_pow_embedding
    [Normal k Ω] (p : ℕ) [Fact p.Prime] [CharP k p]
    (n : ℕ) (hΩ : Module.finrank k Ω = p ^ n)
    (g : L →ₐ[k] Ω) (hL : 1 < Module.finrank k L) :
    ∃ P : IntermediateField k L, Normal k P ∧ Module.finrank k P = p := by
  by_cases hbot : separableClosure k L = ⊥
  · let : IsPurelyInseparable k L := separableClosure.eq_bot_iff.mp hbot
    obtain ⟨P, hP, hdegree⟩ := exists_prime_subfield_of_isPurelyInseparable p hL
    let : IsPurelyInseparable k P := hP
    exact ⟨P, inferInstance, hdegree⟩
  have hG : IsPGroup p (separableClosure k Ω ≃ₐ[k] separableClosure k Ω) := by
    apply IsPGroup.of_card_dvd_pow (n := n)
    rw [IsGalois.card_aut_eq_finrank, ← hΩ,
      ← Module.finrank_mul_finrank k (separableClosure k Ω) Ω]
    exact Nat.dvd_mul_right _ _
  let j : separableClosure k L →ₐ[k] separableClosure k Ω :=
    (g.comp (separableClosure k L).val).codRestrict (separableClosure k Ω).toSubalgebra
      (fun x => (map_mem_separableClosure_iff g).mpr x.property)
  have hsep : 1 < Module.finrank k (separableClosure k L) :=
    lt_of_le_of_ne (Nat.succ_le_of_lt Module.finrank_pos)
      (fun h => hbot (finrank_eq_one_iff.mp h.symm))
  obtain ⟨r, _, _, hr, hnormal, hdegree, ⟨i⟩⟩ :=
    Field.exists_separable_normal_prime_presentation_of_isPGroup_embedding p hG j hsep
  let : Fact (Irreducible r) := ⟨hr⟩
  let : Normal k (AdjoinRoot r) := hnormal
  let f : AdjoinRoot r →ₐ[k] L := (separableClosure k L).val.comp i
  refine ⟨f.fieldRange, Normal.of_algEquiv f.equivFieldRange, ?_⟩
  rw [← f.equivFieldRange.toLinearEquiv.finrank_eq, (AdjoinRoot.powerBasis hr.ne_zero).finrank]
  exact hdegree

end IntermediateField
