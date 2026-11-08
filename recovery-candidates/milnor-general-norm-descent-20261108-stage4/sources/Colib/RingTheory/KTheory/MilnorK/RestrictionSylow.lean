/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.RestrictionKernel
public import Colib.FieldTheory.SylowFixedField

/-!
# Joint detection by actual Sylow fixed-field restrictions

For a finite Galois overfield, restrictions to one Sylow fixed field for each
prime jointly detect the original Milnor ring and each homogeneous group.
Their kernels have annihilators prime to the corresponding prime. No rational
coefficients, canonical transfer, choice-independent norm, or tower law is used.

This adapts `Aglib/KTheory/MilnorK/RestrictionSylow.lean` at revision
`52e09db47998f139064acf48a2d3a64494d0dd9a` directly to native Stacks maps.
All fields share the universe of the native norm, with arbitrary characteristic.
-/

@[expose] public noncomputable section

universe u

namespace Stacks.Chow

private theorem eq_zero_of_prime_coprime_annihilators {A : Type*} [AddGroup A]
    (x : A) (hx : ∀ p : ℕ, p.Prime → ∃ m : ℕ, p.Coprime m ∧ m • x = 0) : x = 0 := by
  apply AddMonoid.addOrderOf_eq_one_iff.mp
  by_contra h
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd h
  obtain ⟨m, hm, hmx⟩ := hx p hp
  exact (hp.coprime_iff_not_dvd.mp hm)
    (hpd.trans (addOrderOf_dvd_iff_nsmul_eq_zero.mpr hmx))

variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω]
  [FiniteDimensional k Ω] [IsGalois k Ω]

/-- Restrictions to actual Sylow fixed fields jointly detect every native
Milnor ring class. A different Sylow subgroup may be chosen at each prime. -/
theorem eq_zero_of_milnorKRingMap_sylow_restrictions (x : MilnorKRing k)
    (hx : ∀ (p : ℕ) (_hp : p.Prime),
      ∃ S : Sylow p (Ω ≃ₐ[k] Ω),
        milnorKRingMap (algebraMap k
          (IntermediateField.fixedField (S : Subgroup (Ω ≃ₐ[k] Ω)))) x = 0) : x = 0 := by
  apply eq_zero_of_prime_coprime_annihilators x
  intro p hp
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, hS⟩ := hx p hp
  refine ⟨Module.finrank k (IntermediateField.fixedField (S : Subgroup (Ω ≃ₐ[k] Ω))),
    IntermediateField.coprime_finrank_sylow_fixedField p S, ?_⟩
  simpa only [natCast_zsmul] using finrank_zsmul_eq_zero_of_milnorKRingMap_eq_zero k
    (IntermediateField.fixedField (S : Subgroup (Ω ≃ₐ[k] Ω))) x hS

/-- Equality on the whole native ring can be tested after the actual Sylow
fixed-field restrictions. -/
theorem eq_of_milnorKRingMap_sylow_restrictions (x y : MilnorKRing k)
    (hxy : ∀ (p : ℕ) (_hp : p.Prime),
      ∃ S : Sylow p (Ω ≃ₐ[k] Ω),
        milnorKRingMap (algebraMap k
          (IntermediateField.fixedField (S : Subgroup (Ω ≃ₐ[k] Ω)))) x =
        milnorKRingMap (algebraMap k
          (IntermediateField.fixedField (S : Subgroup (Ω ≃ₐ[k] Ω)))) y) : x = y := by
  apply sub_eq_zero.mp
  apply eq_zero_of_milnorKRingMap_sylow_restrictions k Ω (x - y)
  intro p hp
  obtain ⟨S, hS⟩ := hxy p hp
  exact ⟨S, by rw [map_sub, hS, sub_self]⟩

/-- Joint detection on every original homogeneous group, with degree zero
included and no characteristic restriction. -/
theorem eq_zero_of_milnorKTransport_sylow_restrictions (n : ℕ) (x : MilnorKTheory k n)
    (hx : ∀ (p : ℕ) (_hp : p.Prime),
      ∃ S : Sylow p (Ω ≃ₐ[k] Ω),
        milnorKTransport (algebraMap k
          (IntermediateField.fixedField (S : Subgroup (Ω ≃ₐ[k] Ω)))) n x = 0) : x = 0 := by
  apply Subtype.ext
  apply eq_zero_of_milnorKRingMap_sylow_restrictions k Ω (x : MilnorKRing k)
  intro p hp
  obtain ⟨S, hS⟩ := hx p hp
  exact ⟨S, congrArg Subtype.val hS⟩

/-- Equality in every original homogeneous group descends through the actual
Sylow fixed-field restrictions. -/
theorem eq_of_milnorKTransport_sylow_restrictions (n : ℕ) (x y : MilnorKTheory k n)
    (hxy : ∀ (p : ℕ) (_hp : p.Prime),
      ∃ S : Sylow p (Ω ≃ₐ[k] Ω),
        milnorKTransport (algebraMap k
          (IntermediateField.fixedField (S : Subgroup (Ω ≃ₐ[k] Ω)))) n x =
        milnorKTransport (algebraMap k
          (IntermediateField.fixedField (S : Subgroup (Ω ≃ₐ[k] Ω)))) n y) : x = y := by
  apply sub_eq_zero.mp
  apply eq_zero_of_milnorKTransport_sylow_restrictions k Ω n (x - y)
  intro p hp
  obtain ⟨S, hS⟩ := hxy p hp
  exact ⟨S, by rw [map_sub, hS, sub_self]⟩

end Stacks.Chow
