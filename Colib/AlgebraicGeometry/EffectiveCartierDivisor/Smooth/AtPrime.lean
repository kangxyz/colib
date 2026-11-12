/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Divisors.PolynomialEvaluationFrame
public import Colib.RingTheory.Etale.PrimeParameter
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisor.ZeroIdeal

/-!
# Smooth effective Cartier divisors through points of positive local dimension

The étale line chart retains an element of the original prime ideal as its
line coordinate. The actual zero fiber is the flat pullback of polynomial
evaluation at zero. The open-range isomorphism identifies this fiber with
an effective Cartier divisor in the original smooth scheme's affine open.

Adapted from Motivic at a6805c4a87cdfd7717dd7a94039246a167f15380,
`Motivic/Aglib/AlgebraicGeometry/EffectiveCartierDivisor/Smooth/SmoothCartierAtPrime.lean`,
blob `aecb161b698afe54a7a000f640c17b596744a8b9`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Stacks.Divisors

universe u

namespace AlgebraicGeometry.Scheme

/-- The literal zero fiber gives a smooth effective Cartier divisor through
the original prime's lift to a principal neighborhood. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/AlgebraicGeometry/EffectiveCartierDivisor/Smooth/SmoothCartierAtPrime.lean:24-66"
  "adaptation" "The original zero fiber, with the actual kernel ideal effective Cartier"]
theorem exists_smooth_cartier_at_prime
    (k R : Type u) [Field k] [PerfectField k] [CommRing R]
    [Algebra k R] [Algebra.Smooth k R] (p : Ideal R) [p.IsPrime]
    (hpos : 0 < ringKrullDim (Localization.AtPrime p)) :
    ∃ r ∉ p, ∃ (Z : Scheme.{u}) (i : Z ⟶ Spec (.of (Localization.Away r))),
      IsClosedImmersion i ∧ IsEffectiveCartierDivisor i.ker ∧
      Smooth (i ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away r)))) ∧
      ∃ q : Spec (.of (Localization.Away r)),
        (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))) q =
          (⟨p, inferInstance⟩ : PrimeSpectrum R) ∧ q ∈ Set.range i := by
  classical
  obtain ⟨f, hf, d, c, r, hr, ψ, hψ, hX⟩ :=
    Algebra.exists_prime_parameter_etale_line_chart k R p hpos
  let B := MvPolynomial {j : Fin d // j ≠ c} k
  let Y := Spec (.of (Localization.Away r))
  let h : Y ⟶ Spec (.of (Polynomial B)) := Spec.map (CommRingCat.ofHom ψ.toRingHom)
  have : Etale h := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr hψ
  let z := RelativeCurvePencil.evaluationGraph B 0
  have : IsClosedImmersion z :=
    inferInstanceAs (IsClosedImmersion (RelativeCurvePencil.evaluationGraph B 0))
  let i := pullback.snd z h
  have hI : IsEffectiveCartierDivisor i.ker := by
    rw [ker_eq_comap_ker_of_isPullback (IsPullback.of_hasPullback z h).flip]
    exact isPullbackDefined_of_flat h z.ker
      (RelativeCurvePencil.evaluationGraphIdeal_isEffectiveCartierDivisor B 0)
  have hw : i ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away r))) =
      pullback.fst z h ≫ Spec.map (CommRingCat.ofHom (algebraMap k B)) := by
    have ha : h ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial B))) =
        Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away r))) := by
      rw [← Spec.map_comp]
      congr 1
      exact CommRingCat.hom_ext ψ.comp_algebraMap
    rw [← ha]
    dsimp only [i]
    rw [← pullback.condition_assoc]
    congr 1
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    ext a
    simp
  have hsm : Smooth (i ≫ Spec.map
      (CommRingCat.ofHom (algebraMap k (Localization.Away r)))) := by
    rw [hw]
    have : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k B))) :=
      (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
        ((RingHom.smooth_algebraMap (R := k) (S := B)).mpr inferInstance)
    infer_instance
  have hp : (⟨p, inferInstance⟩ : PrimeSpectrum R) ∈
      Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away r))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
    exact hr
  obtain ⟨q, hq⟩ := hp
  refine ⟨r, hr, pullback z h, i, inferInstance, hI, hsm, q, hq, ?_⟩
  have hqX : Polynomial.X ∈ (h q).asIdeal := by
    change ψ Polynomial.X ∈ q.asIdeal
    rw [hX]
    have he := congrArg (fun t : PrimeSpectrum R ↦ f ∈ t.asIdeal) hq
    exact he.mpr hf
  change q ∈ Set.range (pullback.snd z h)
  rw [Scheme.Pullback.range_snd]
  change h q ∈ Set.range (PrimeSpectrum.comap (Polynomial.evalRingHom (0 : B)))
  rw [range_comap_of_surjective _ _ (fun b ↦ ⟨Polynomial.C b, by simp⟩)]
  rw [PrimeSpectrum.mem_zeroLocus, Polynomial.ker_evalRingHom]
  simp only [Polynomial.C_0, sub_zero]
  exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hqX)

/-- Every positive dimensional point of a smooth scheme over a perfect field
lies on a smooth effective Cartier divisor in an affine open neighborhood. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/AlgebraicGeometry/EffectiveCartierDivisor/Smooth/SmoothCartierAtPrime.lean:71-126"
  "adaptation" "The actual affine open, divisor kernel, base map and point image"]
theorem exists_smooth_cartier_neighborhood
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [Smooth p] (x : X)
    (hpos : 0 < ringKrullDim (X.presheaf.stalk x)) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
      ∃ (Z : Scheme.{u}) (i : Z ⟶ U.toScheme),
        IsClosedImmersion i ∧ IsEffectiveCartierDivisor i.ker ∧
        Smooth (i ≫ U.ι ≫ p) ∧ x ∈ Set.range (i ≫ U.ι) := by
  obtain ⟨R, a, ha, q, hq⟩ := X.exists_Spec_apply_eq x
  let : IsOpenImmersion a := ha
  let φ : k →+* R := (Spec.preimage (a ≫ p)).hom
  let : Algebra k R := φ.toAlgebra
  have hφ : Spec.map (CommRingCat.ofHom (algebraMap k R)) = a ≫ p :=
    Spec.map_preimage _
  have : Algebra.Smooth k R := by
    apply (RingHom.smooth_algebraMap (R := k) (S := R)).mp
    apply (HasRingHomProperty.Spec_iff (P := @Smooth)).mp
    rw [Spec.map_preimage]
    infer_instance
  have hqpos : 0 < ringKrullDim (Localization.AtPrime q.asIdeal) := by
    let e := asIso (a.stalkMap q) ≪≫ Spec.stalkIso R q
    rw [← ringKrullDim_eq_of_ringEquiv e.commRingCatIsoToRingEquiv]
    change 0 < ringKrullDim (X.presheaf.stalk (a q))
    rw [hq]
    exact hpos
  obtain ⟨r, _, Z, i, hi, hI, hs, y, hy, hz⟩ :=
    exists_smooth_cartier_at_prime k R q.asIdeal hqpos
  let : IsClosedImmersion i := hi
  let a' : Spec (.of (Localization.Away r)) ⟶ X :=
    Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))) ≫ a
  let U := a'.opensRange
  let e : Spec (.of (Localization.Away r)) ≅ U.toScheme :=
    IsOpenImmersion.isoOfRangeEq a' U.ι (by simp [U])
  have he : e.hom ≫ U.ι = a' := IsOpenImmersion.isoOfRangeEq_hom_fac ..
  let j : Z ⟶ U.toScheme := i ≫ e.hom
  have hu : a' ≫ p =
      Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away r))) := by
    dsimp only [a']
    rw [Category.assoc, ← hφ, ← Spec.map_comp]
    rfl
  have hyu : a' y = x := by
    change a ((Spec.map
      (CommRingCat.ofHom (algebraMap R (Localization.Away r)))) y) = x
    rw [hy]
    exact hq
  have hj : j ≫ U.ι = i ≫ a' := by
    dsimp only [j]
    rw [Category.assoc, he]
  have hI' : IsEffectiveCartierDivisor j.ker := by
    have hpb : IsPullback j (𝟙 Z) e.inv i := IsPullback.of_vert_isIso ⟨by simp [j]⟩
    rw [ker_eq_comap_ker_of_isPullback hpb]
    exact isPullbackDefined_of_flat e.inv i.ker hI
  refine ⟨U, isAffineOpen_opensRange a', ⟨y, hyu⟩, Z, j, inferInstance, hI', ?_, ?_⟩
  · rw [← Category.assoc, hj, Category.assoc, hu]
    exact hs
  · obtain ⟨z, hz⟩ := hz
    refine ⟨z, ?_⟩
    rw [hj]
    change a' (i z) = x
    rw [hz]
    exact hyu

end AlgebraicGeometry.Scheme
