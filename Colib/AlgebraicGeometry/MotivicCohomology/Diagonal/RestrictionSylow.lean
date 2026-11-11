/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.CorestrictionDegree
public import Colib.FieldTheory.SylowFixedField

/-!
# Sylow restrictions detect classes on the raw diagonal

The actual finite transfer kills each restriction kernel by the degree of
its fixed field. For every prime the corresponding Sylow fixed field has
degree prime to that prime, so these kernels have trivial intersection.

Adapted from `Motivic/Cohomology/Diagonal/RestrictionSylow.lean:26-57`
at `a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section

universe u

namespace AlgebraicGeometry.MotivicCohomology.DiagonalRestrictionSylow

open PresheafWithTransfers DiagonalCorestriction DiagonalFieldChange

variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω]
  [FiniteDimensional k Ω] [IsGalois k Ω]

/-- The actual restrictions to one Sylow fixed field for each prime jointly
detect zero in the original raw diagonal group. -/
@[colib_ref "motivic_source_a6805c4" "Motivic/Cohomology/Diagonal/RestrictionSylow.lean:26-43"
  "adaptation" "The finite degree law for native raw diagonal restriction and transfer"]
theorem eq_zero_of_sylow_restrictions (n : ℕ)
    (x : (motivicRawBaseComplex k n).homology n)
    (hx : ∀ (p : ℕ), p.Prime → ∃ S : Sylow p (Ω ≃ₐ[k] Ω),
      fieldChange (algebraMap k
        (IntermediateField.fixedField (S : Subgroup (Ω ≃ₐ[k] Ω)))) n x = 0) :
    x = 0 := by
  apply AddMonoid.addOrderOf_eq_one_iff.mp
  by_contra h
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd h
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, hS⟩ := hx p hp
  let L := IntermediateField.fixedField (S : Subgroup (Ω ≃ₐ[k] Ω))
  have hdegree : (Module.finrank k L : ℤ) • x = 0 := by
    rw [← corestriction_fieldChange (E := L) n x, hS, map_zero]
  have hdiv : addOrderOf x ∣ Module.finrank k L :=
    addOrderOf_dvd_iff_nsmul_eq_zero.mpr (by simpa only [natCast_zsmul] using hdegree)
  exact (hp.coprime_iff_not_dvd.mp (IntermediateField.coprime_finrank_sylow_fixedField p S))
    (hpd.trans hdiv)

/-- Equality on the original raw diagonal descends through the actual Sylow
fixed-field restrictions. -/
theorem eq_of_sylow_restrictions (n : ℕ)
    (x y : (motivicRawBaseComplex k n).homology n)
    (hxy : ∀ (p : ℕ), p.Prime → ∃ S : Sylow p (Ω ≃ₐ[k] Ω),
      fieldChange (algebraMap k
        (IntermediateField.fixedField (S : Subgroup (Ω ≃ₐ[k] Ω)))) n x =
      fieldChange (algebraMap k
        (IntermediateField.fixedField (S : Subgroup (Ω ≃ₐ[k] Ω)))) n y) :
    x = y := by
  apply sub_eq_zero.mp
  apply eq_zero_of_sylow_restrictions k Ω n (x - y)
  intro p hp
  obtain ⟨S, hS⟩ := hxy p hp
  exact ⟨S, by rw [map_sub, hS, sub_self]⟩

end AlgebraicGeometry.MotivicCohomology.DiagonalRestrictionSylow
