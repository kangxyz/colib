/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Mathlib.RingTheory.Smooth.Field
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Nonzero residue differentials from original prime ideals

Over a perfect field, the conormal map for the residue field of a local
ring is injective under the stated smoothness and finite type hypotheses.
A positive dimensional regular local ring supplies a nonzero conormal
class. Clearing denominators preserves its nonzero residue differential
and supplies an element in the original prime ideal.

Adapted from Motivic at a6805c4a87cdfd7717dd7a94039246a167f15380,
`Motivic/Aglib/RingTheory/Kaehler/{LocalParameterDifferential,PrimeParameterDifferential}.lean`.
-/

@[expose] public noncomputable section

open Module TensorProduct IsLocalRing

universe u v

namespace KaehlerDifferential

private theorem exists_maximalIdeal_residue_differential_ne_zero
    (k : Type u) (A : Type v) [Field k] [PerfectField k] [CommRing A]
    [Algebra k A] [IsRegularLocalRing A]
    [Algebra.FormallySmooth k A] [Algebra.EssFiniteType k (ResidueField A)]
    (hpos : 0 < ringKrullDim A) :
    ∃ f ∈ maximalIdeal A, (1 ⊗ₜ[A] D k A f : ResidueField A ⊗[A] Ω[A⁄k]) ≠ 0 := by
  have hdim := (IsRegularLocalRing.iff_finrank_cotangentSpace (R := A)).mp
    (inferInstance : IsRegularLocalRing A)
  have hfin : 0 < Module.finrank (ResidueField A) (CotangentSpace A) := by
    exact_mod_cast hdim ▸ hpos
  have hker : RingHom.ker (algebraMap A (ResidueField A)) = maximalIdeal A := ker_residue
  have : Nontrivial (CotangentSpace A) := Module.nontrivial_of_finrank_pos hfin
  have : Nontrivial (RingHom.ker (algebraMap A (ResidueField A))).Cotangent := by
    rw [hker]
    infer_instance
  obtain ⟨x, hx⟩ := exists_ne (0 : (RingHom.ker (algebraMap A (ResidueField A))).Cotangent)
  obtain ⟨f, hf⟩ := (RingHom.ker (algebraMap A (ResidueField A))).toCotangent_surjective x
  have hinj : Function.Injective (kerCotangentToTensor k A (ResidueField A)) :=
    (Algebra.FormallySmooth.kerCotangentToTensor_injective_iff residue_surjective).mpr
      inferInstance
  refine ⟨f, hker ▸ f.property, ?_⟩
  intro hz
  have hz' : kerCotangentToTensor k A (ResidueField A) (Ideal.toCotangent _ f) = 0 := hz
  have hh := hinj (hz'.trans (map_zero _).symm)
  exact hx (hf.symm.trans hh)

/-- Clearing the local parameter's denominator gives an original prime element
whose residue differential is nonzero. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/RingTheory/Kaehler/PrimeParameterDifferential.lean:19-53"
  "adaptation" "A nonzero residue differential of an element of the original prime"]
theorem exists_prime_residue_differential_ne_zero
    (k : Type u) (R : Type v) [Field k] [PerfectField k] [CommRing R]
    [Algebra k R] [Algebra.Smooth k R] (p : Ideal R) [p.IsPrime]
    [IsRegularLocalRing (Localization.AtPrime p)]
    (hpos : 0 < ringKrullDim (Localization.AtPrime p)) :
    ∃ f ∈ p, (1 ⊗ₜ[R] D k R f :
      ResidueField (Localization.AtPrime p) ⊗[R] Ω[R⁄k]) ≠ 0 := by
  let A := Localization.AtPrime p
  let K := ResidueField A
  have : Algebra.EssFiniteType k A := .comp k R A
  have : Algebra.EssFiniteType k K := .comp k A K
  obtain ⟨f, hf, hdf⟩ := exists_maximalIdeal_residue_differential_ne_zero k A hpos
  obtain ⟨a, s, hs⟩ := IsLocalization.exists_mk'_eq p.primeCompl f
  have ha : a ∈ p := (IsLocalization.AtPrime.mk'_mem_maximal_iff A p a s).mp (hs ▸ hf)
  refine ⟨a, ha, ?_⟩
  intro hz
  let L : K ⊗[R] Ω[R⁄k] →ₗ[K] K ⊗[A] Ω[A⁄k] :=
    (TensorProduct.mapOfCompatibleSMul A R K K Ω[A⁄k]).comp
      (AlgebraTensorModule.map (LinearMap.id : K →ₗ[K] K) (KaehlerDifferential.map k k R A))
  have hza : (1 ⊗ₜ[A] D k A (algebraMap R A a) : K ⊗[A] Ω[A⁄k]) = 0 := by
    have hh := congrArg L hz
    simpa only [L, LinearMap.comp_apply, AlgebraTensorModule.map_tmul,
      LinearMap.id_apply, TensorProduct.mapOfCompatibleSMul_tmul,
      KaehlerDifferential.map_D, map_zero] using hh
  have hae : algebraMap R A a = f * algebraMap R A s :=
    IsLocalization.mk'_eq_iff_eq_mul.mp hs
  have hf0 : algebraMap A K f = 0 := (residue_eq_zero_iff f).mpr hf
  have hsu : IsUnit (algebraMap R K s) :=
    (IsLocalization.map_units A s).map (algebraMap A K)
  rw [hae, Derivation.leibniz, tmul_add, tmul_smul, tmul_smul,
    smul_tmul', smul_tmul', Algebra.smul_def, Algebra.smul_def,
    mul_one, mul_one, hf0, zero_tmul, zero_add] at hza
  have hs0 : algebraMap A K (algebraMap R A s) ≠ 0 := hsu.ne_zero
  have : (1 ⊗ₜ[A] D k A f : K ⊗[A] Ω[A⁄k]) = 0 := by
    apply (smul_eq_zero.mp ?_).resolve_left hs0
    simpa only [smul_tmul', smul_eq_mul, mul_one] using hza
  exact hdf this

end KaehlerDifferential
