/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.PolynomialChartFreeness
public import Colib.AlgebraicGeometry.RelativeCurve.ProjectiveMap.NativePolynomialCharts
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat

/-!
# Finite local freeness on the original coefficient restriction

The two actual polynomial charts of the same localized compactification
cover its whole target. Their section modules give flatness on the literal
restriction of the original finite map.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option quotPrecheck false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Morphisms
open scoped Polynomial

attribute [local instance] Polynomial.algebra

universe u

namespace AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification

open RelativeCurve.NativeProjectiveLine

variable (R : Type u) [CommRing R] [IsNoetherianRing R]
  {C : Scheme.{u}} (f : C ⟶ projectiveSpaceOverRing 1 (.of R)) [IsFinite f]
  (r : R)

local notation "π" => (projectiveSpaceOverRing 1 (.of R) ↘ Spec (.of R))
local notation "B" => (Localization.Away r)[X]
local notation "ℓ" => (Spec.map (CommRingCat.ofHom (algebraMap R[X] B)))
local notation "W" => (π ⁻¹ᵁ PrimeSpectrum.basicOpen r)

omit [IsNoetherianRing R] in
private theorem localizationPolynomial_range : Set.range ℓ = (PrimeSpectrum.basicOpen
    (Polynomial.C r) : Set (PrimeSpectrum R[X])) := by
  let : IsLocalization.Away (Polynomial.C r) B := by
    have h := Polynomial.isLocalization (Submonoid.powers r) (Localization.Away r)
    rwa [Submonoid.map_powers] at h
  exact PrimeSpectrum.localization_away_comap_range B (Polynomial.C r)

/-- Free actual chart sections imply finite local freeness on every actual
coefficient open inside the chosen principal localization. -/
theorem finiteLocallyFree_restrict_of_free_polynomialCharts
    (hfree : ∀ i : Fin 2,
      let q := pullback.snd f (ℓ ≫ polynomialCharts R i)
      letI : Algebra B Γ(pullback f (ℓ ≫ polynomialCharts R i), ⊤) :=
        (specSectionsMap q).toAlgebra
      Module.Free B Γ(pullback f (ℓ ≫ polynomialCharts R i), ⊤))
    (O : (Spec (.of R)).Opens) (hO : O ≤ PrimeSpectrum.basicOpen r) :
    IsFiniteLocallyFree (f ∣_ (π ⁻¹ᵁ O)) := by
  let : IsLocalization.Away (Polynomial.C r) B := by
    have h := Polynomial.isLocalization (Submonoid.powers r) (Localization.Away r)
    rwa [Submonoid.map_powers] at h
  let : IsOpenImmersion ℓ := IsOpenImmersion.of_isLocalization (Polynomial.C r)
  have hRange (i : Fin 2) : Set.range (ℓ ≫ polynomialCharts R i) ⊆ Set.range (W).ι := by
    rintro _ ⟨x, rfl⟩
    rw [Opens.range_ι]
    have hx : ℓ x ∈ (PrimeSpectrum.basicOpen (Polynomial.C r) : Set (PrimeSpectrum R[X])) := by
      rw [← localizationPolynomial_range R r]
      exact ⟨x, rfl⟩
    change π (polynomialCharts R i (ℓ x)) ∈ PrimeSpectrum.basicOpen r
    rw [← Hom.comp_apply, polynomialCharts_projection]
    exact hx
  let c (i : Fin 2) := IsOpenImmersion.lift (W).ι (ℓ ≫ polynomialCharts R i) (hRange i)
  have hc (i : Fin 2) : c i ≫ (W).ι = ℓ ≫ polynomialCharts R i := IsOpenImmersion.lift_fac ..
  let (i : Fin 2) : IsOpenImmersion (c i) := by
    have : IsOpenImmersion (c i ≫ (W).ι) := hc i ▸ inferInstanceAs
      (IsOpenImmersion (ℓ ≫ polynomialCharts R i))
    exact IsOpenImmersion.of_comp (c i) (W).ι
  let 𝒰 : (W).toScheme.OpenCover :=
    { I₀ := Fin 2
      X := fun _ ↦ Spec (.of B)
      f := c
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        refine ⟨fun x ↦ ?_, inferInstance⟩
        obtain ⟨i, y, hy⟩ := exists_mem_range_polynomialCharts R ((W).ι x)
        have hy' : y ∈ (PrimeSpectrum.basicOpen (Polynomial.C r) : Set (PrimeSpectrum R[X])) := by
          have hxy : π ((W).ι x) ∈ PrimeSpectrum.basicOpen r := x.property
          rw [← hy, ← Hom.comp_apply, polynomialCharts_projection] at hxy
          exact hxy
        obtain ⟨z, hz⟩ := (localizationPolynomial_range R r).symm ▸ hy'
        refine ⟨i, z, (W).ι.isOpenEmbedding.injective ?_⟩
        rw [← Hom.comp_apply, hc, Hom.comp_apply, hz, hy] }
  have hflat : Flat (f ∣_ W) := by
    refine (IsZariskiLocalAtTarget.iff_of_openCover (P := @Flat) 𝒰).2 fun i ↦ ?_
    change Flat (pullback.snd (f ∣_ W) (c i))
    let q := pullback.snd f (ℓ ≫ polynomialCharts R i)
    let : IsAffine (pullback f (ℓ ≫ polynomialCharts R i)) := isAffine_of_isAffineHom q
    let : Algebra B Γ(pullback f (ℓ ≫ polynomialCharts R i), ⊤) :=
      (specSectionsMap q).toAlgebra
    let : Module.Free B Γ(pullback f (ℓ ≫ polynomialCharts R i), ⊤) := hfree i
    have hspec : Flat (Spec.map (CommRingCat.ofHom (specSectionsMap q))) :=
      Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
    rw [Spec_map_specSectionsMap q] at hspec
    let : Flat q := (MorphismProperty.cancel_left_of_respectsIso @Flat _ _).mp hspec
    let H := (IsPullback.of_hasPullback (f ∣_ W) (c i)).paste_horiz
      (isPullback_morphismRestrict f W).flip
    let e := H.isoPullback ≪≫ pullback.congrHom rfl (hc i)
    have he : e.hom ≫ q = pullback.snd (f ∣_ W) (c i) := by
      simp only [e, q, Iso.trans_hom, Category.assoc, pullback.congrHom_hom,
        pullback.map, pullback.lift_snd, Category.comp_id, IsPullback.isoPullback_hom_snd]
    have hf : Flat (e.hom ≫ q) := inferInstance
    rwa [he] at hf
  let : Flat (f ∣_ W) := hflat
  let V := π ⁻¹ᵁ O
  have hVW : V ≤ W := by
    intro x hx
    change π x ∈ PrimeSpectrum.basicOpen r
    exact hO hx
  have himage : (W).ι ''ᵁ ((W).ι ⁻¹ᵁ V) = V := by
    rw [Hom.image_preimage_eq_opensRange_inf, Opens.opensRange_ι, inf_eq_right.mpr hVW]
  have h' : Flat ((f ∣_ W) ∣_ ((W).ι ⁻¹ᵁ V)) := inferInstance
  have h'' := (MorphismProperty.arrow_mk_iso_iff (P := @Flat)
    (morphismRestrictRestrict f W ((W).ι ⁻¹ᵁ V))).mp h'
  let : Flat (f ∣_ V) := himage ▸ h''
  let : IsLocallyNoetherian V.toScheme := LocallyOfFiniteType.isLocallyNoetherian (V.ι ≫ π)
  exact (isFiniteLocallyFree_iff_isFinite_flat_of_isLocallyNoetherian _).2
    ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification
