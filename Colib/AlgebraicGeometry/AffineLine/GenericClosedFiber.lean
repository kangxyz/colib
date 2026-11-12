/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Scheme.PolynomialQuotient.Ambient
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-! # Proper closed sets in the generic affine-line fiber

A closed set avoiding the generic point of the original polynomial spectrum
has finite fiber over the generic point of the coefficient spectrum.
The affine calculation supplies the corresponding chart in Motivic's
`Normalization/Compactification/Boundary/RelativeInfinityFiniteBaseOpen.lean`
at `a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Polynomial

universe u

namespace AlgebraicGeometry.Scheme

open PolynomialLaurent

private theorem finite_closed_polynomial_set {K : Type u} [Field K]
    {Z : Set (Spec (.of K[X]))} (hZ : IsClosed Z)
    (hη : genericPoint (Spec (.of K[X])) ∉ Z) : Z.Finite := by
  obtain ⟨I, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal Z).mp hZ
  have hI : I ≠ ⊥ := by
    intro h
    exact hη (by rw [h, PrimeSpectrum.zeroLocus_bot]; trivial)
  obtain ⟨f, hf, hf₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  change Polynomial K at f
  let : Module.Finite K (AdjoinRoot f) := (AdjoinRoot.powerBasis hf₀).finite
  let : IsArtinianRing (AdjoinRoot f) := IsArtinianRing.of_finite K _
  have hfin := Set.finite_range (PrimeSpectrum.comap (AdjoinRoot.mk f))
  let m : Polynomial K →+* AdjoinRoot f := AdjoinRoot.mk f
  have hm : Function.Surjective m := AdjoinRoot.mk_surjective
  have hr := range_comap_of_surjective (AdjoinRoot f) m hm
  change Set.range (PrimeSpectrum.comap (AdjoinRoot.mk f)) =
    PrimeSpectrum.zeroLocus (RingHom.ker (Ideal.Quotient.mk (Ideal.span {f}))) at hr
  rw [Ideal.mk_ker] at hr
  rw [hr] at hfin
  exact hfin.subset (PrimeSpectrum.zeroLocus_anti_mono_ideal
    ((Ideal.span_singleton_le_iff_mem I).mpr hf))

/-- The part of a closed set over the coefficient generic point is finite if
the set avoids the generic point of the original polynomial line. -/
theorem finite_polynomialProjection_generic_preimage_inter_closed
    (R : Type u) [CommRing R] [IsDomain R] {Z : Set (Spec (.of R[X]))}
    (hZ : IsClosed Z) (hη : genericPoint (Spec (.of R[X])) ∉ Z) :
    (Z ∩ (polynomialProjection (.of R) ⁻¹' {genericPoint (Spec (.of R))})).Finite := by
  let K := FractionRing R
  let φ : R →+* K := algebraMap R K
  let b := Spec.map (CommRingCat.ofHom φ)
  let d := Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom φ))
  have hinj : Function.Injective φ := IsFractionRing.injective R K
  have hb : b (⊥ : PrimeSpectrum K) = genericPoint (Spec (.of R)) := by
    apply PrimeSpectrum.ext
    rw [genericPoint_eq_bot_of_affine]
    exact Ideal.comap_bot_of_injective φ hinj
  have hd : d (genericPoint (Spec (.of K[X]))) = genericPoint (Spec (.of R[X])) := by
    rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
    apply PrimeSpectrum.ext
    exact Ideal.comap_bot_of_injective (Polynomial.mapRingHom φ)
      (Polynomial.map_injective φ hinj)
  have hfinite : (d ⁻¹' Z).Finite := finite_closed_polynomial_set
    (hZ.preimage d.continuous) (by
      change d (genericPoint (Spec (.of K[X]))) ∉ Z
      rw [hd]
      exact hη)
  refine (hfinite.image d).subset ?_
  intro y hy
  have hy' : polynomialProjection (.of R) y = genericPoint (Spec (.of R)) := hy.2
  have H := PolynomialOpenQuotient.ambient_isPullback φ
  obtain ⟨x, _, hx⟩ := Scheme.exists_preimage_of_isPullback H
    (⊥ : PrimeSpectrum K) y (hb.trans hy'.symm)
  refine ⟨x, ?_, hx⟩
  change d x ∈ Z
  exact hx.symm ▸ hy.1

end AlgebraicGeometry.Scheme
