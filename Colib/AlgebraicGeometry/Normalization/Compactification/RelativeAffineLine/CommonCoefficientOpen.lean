/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.FiniteBoundary
public import Colib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.PolynomialChartFreeness

/-!
# A common coefficient open for the free charts and the finite boundary

The two whole polynomial charts have one coefficient denominator. The
finite-boundary neighborhood contains the generic point of the same
coefficient scheme, so an affine open meets both requirements.

Adapted from Motivic at a6805c4a87cdfd7717dd7a94039246a167f15380,
`Normalization/Compactification/RelativeAffineLine/CommonCoefficientOpen.lean`
under `Motivic/Aglib/AlgebraicGeometry`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Polynomial

attribute [local instance] Polynomial.algebra

universe u

namespace AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification

private theorem finite_restrict_of_le {X S : Scheme.{u}} (f : X ⟶ S)
    {V O : S.Opens} (h : O ≤ V) [IsFinite (f ∣_ V)] : IsFinite (f ∣_ O) := by
  have hf : IsFinite ((f ∣_ V) ∣_ (V.ι ⁻¹ᵁ O)) := inferInstance
  have h' := (MorphismProperty.arrow_mk_iso_iff (P := @IsFinite)
    (morphismRestrictRestrict f V (V.ι ⁻¹ᵁ O))).mp hf
  have he : V.ι ''ᵁ (V.ι ⁻¹ᵁ O) = O := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι, inf_eq_right.mpr h]
  rw [he] at h'
  exact h'

/-- The same coefficient localization supplies both free charts, and an
affine open in that localization retains the finite whole boundary. -/
theorem exists_common_coefficient_open
    (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
    (k : Type u) [Field k] [Algebra k R] [Algebra.FiniteType k R]
    {Y : Scheme.{u}} [IsAffine Y] (p : Y ⟶ Spec (.of R[X]))
    [Etale p] [QuasiCompact p] [IsSeparated p]
    (charts : Fin 2 → (Spec (.of R[X]) ⟶ projectiveSpaceOverRing 1 (.of R)))
    [∀ i, IsOpenImmersion (charts i)] :
    ∃ r : R, r ≠ 0 ∧
      (∀ i : Fin 2,
        let A := (Localization.Away r)[X]
        let l := Spec.map (CommRingCat.ofHom (algebraMap R[X] A))
        let q := pullback.snd (toProjectiveLine R p) (l ≫ charts i)
        let : Algebra A Γ(pullback (toProjectiveLine R p) (l ≫ charts i), ⊤) :=
          (specSectionsMap q).toAlgebra
        Module.Free A Γ(pullback (toProjectiveLine R p) (l ≫ charts i), ⊤)) ∧
      ∃ O : (Spec (.of R)).Opens, IsAffineOpen O ∧
        genericPoint (Spec (.of R)) ∈ O ∧ O ≤ PrimeSpectrum.basicOpen r ∧
        IsFinite ((infinityInclusion R p ≫ projection R p) ∣_ O) := by
  let : IsFinite (toProjectiveLine R p) := toProjectiveLine_finite R p k
  obtain ⟨r, hr, hfree⟩ := exists_common_free_polynomial_chart_sections R p charts
  obtain ⟨V, hηV, hfinite⟩ := exists_base_open_finite_infinity R p k
  have hηr : genericPoint (Spec (.of R)) ∈ PrimeSpectrum.basicOpen r := by
    rw [genericPoint_eq_bot_of_affine]
    change r ∉ (⊥ : Ideal R)
    simpa only [Ideal.mem_bot] using hr
  obtain ⟨O, hO, hηO, hOV⟩ := exists_isAffineOpen_mem_and_subset
    (show genericPoint (Spec (.of R)) ∈ V ⊓ PrimeSpectrum.basicOpen r from ⟨hηV, hηr⟩)
  refine ⟨r, hr, hfree, O, hO, hηO, hOV.trans inf_le_right, ?_⟩
  let : IsFinite ((infinityInclusion R p ≫ projection R p) ∣_ V) := hfinite
  exact finite_restrict_of_le _ (hOV.trans inf_le_left)

end AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification
