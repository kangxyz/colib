/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.PurePrimeEquivariance

import Colib.RingTheory.KTheory.MilnorK.Norm.ChosenEquivarianceAcross

/-!
# Norm equivariance in purely inseparable degree dividing a prime

Simultaneous field equivalences preserving the coefficient square carry
pure inseparability by transporting power witnesses. Norm equivariance then
uses the prime comparison or the degree-one separable comparison.
-/

@[expose] public noncomputable section

open Module

universe u

/-- Compatible field equivalences transport pure inseparability. -/
theorem IsPurelyInseparable.of_equiv_equiv
    {K L K' L' : Type*} [Field K] [Field L] [Field K'] [Field L']
    [Algebra K L] [Algebra K' L'] [IsPurelyInseparable K L]
    (σ : K ≃+* K') (τ : L ≃+* L')
    (hστ : τ.toRingHom.comp (algebraMap K L) = (algebraMap K' L').comp σ.toRingHom) :
    IsPurelyInseparable K' L' := by
  obtain ⟨q, _⟩ := ExpChar.exists K
  let : ExpChar K' q := expChar_of_injective_ringHom (f := σ.toRingHom) σ.injective q
  apply (isPurelyInseparable_iff_pow_mem K' q).mpr
  intro y
  obtain ⟨r, b, hb⟩ := IsPurelyInseparable.pow_mem K q (τ.symm y)
  refine ⟨r, σ b, ?_⟩
  calc
    algebraMap K' L' (σ b) = τ (algebraMap K L b) := by
      change ((algebraMap K' L').comp σ.toRingHom) b =
        (τ.toRingHom.comp (algebraMap K L)) b
      exact RingHom.congr_fun hστ.symm b
    _ = τ ((τ.symm y) ^ q ^ r) := congrArg τ hb
    _ = y ^ q ^ r := by rw [map_pow, τ.apply_symm_apply]

namespace Stacks.Chow

variable {K L K' L' : Type u} [Field K] [Field L] [Field K'] [Field L']
  [Algebra K L] [Algebra K' L'] [FiniteDimensional K L] [FiniteDimensional K' L']
  [IsPurelyInseparable K L]

/-- The native chosen norms commute with compatible field equivalences in
purely inseparable degree dividing a prime. -/
theorem milnorKNormRing_map_ringEquiv_of_isPurelyInseparable_of_dvd_prime
    {p : ℕ} (hp : p.Prime) (hdiv : finrank K L ∣ p)
    (σ : K ≃+* K') (τ : L ≃+* L')
    (hστ : τ.toRingHom.comp (algebraMap K L) = (algebraMap K' L').comp σ.toRingHom)
    (x : MilnorKRing L) :
    milnorKRingMap σ.toRingHom (milnorKNormRing K L x) =
      milnorKNormRing K' L' (milnorKRingMap τ.toRingHom x) := by
  rcases (Nat.dvd_prime hp).mp hdiv with hone | hprime
  · have hbij := Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hone
    let : Algebra.IsSeparable K L := ⟨fun y ↦ by
      obtain ⟨a, rfl⟩ := hbij.2 y
      exact isSeparable_algebraMap a⟩
    let : Algebra.IsSeparable K' L' := Algebra.IsSeparable.of_equiv_equiv σ τ hστ.symm
    simpa only [milnorKRingMapLift_eq] using
      milnorKNormRing_map_ringEquiv_across_of_isSeparable σ τ hστ x
  · let : IsPurelyInseparable K' L' := IsPurelyInseparable.of_equiv_equiv σ τ hστ
    exact milnorKNormRing_map_ringEquiv_of_prime_of_isPurelyInseparable
      (hprime.symm ▸ hp) σ τ hστ x

/-- The same equivariance on the original homogeneous groups. -/
theorem milnorKNorm_map_ringEquiv_of_isPurelyInseparable_of_dvd_prime
    {p : ℕ} (hp : p.Prime) (hdiv : finrank K L ∣ p)
    (σ : K ≃+* K') (τ : L ≃+* L')
    (hστ : τ.toRingHom.comp (algebraMap K L) = (algebraMap K' L').comp σ.toRingHom)
    (n : ℕ) (x : MilnorKTheory L n) :
    milnorKTransport σ.toRingHom n (milnorKNorm K L n x) =
      milnorKNorm K' L' n (milnorKTransport τ.toRingHom n x) := by
  apply Subtype.ext
  exact milnorKNormRing_map_ringEquiv_of_isPurelyInseparable_of_dvd_prime hp hdiv σ τ hστ
    (x : MilnorKRing L)

end Stacks.Chow

end
