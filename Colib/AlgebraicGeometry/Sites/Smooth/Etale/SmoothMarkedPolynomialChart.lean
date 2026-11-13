/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.EtaleChartMarkedBaseChange
public import Colib.AlgebraicGeometry.Sites.Smooth.Basic
public import Mathlib.RingTheory.Unramified.LocalStructure

/-! # Actual pointed polynomial coordinates on a smooth affine scheme -/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite

/-- A smooth algebra has an actual principal pointed neighborhood with étale
polynomial coordinates, retaining its original ground-field structure. -/
theorem exists_smooth_affine_marked_polynomial_chart
    (K B Ω : Type u) [Field K] [CommRing B] [Field Ω]
    [Algebra K B] [Algebra.Smooth K B]
    (ξ : Spec (.of Ω) ⟶ Spec (.of B)) :
    ∃ (r : B), r ∉ (ξ default).asIdeal ∧
      ∃ (d : ℕ) (q : Spec (.of (Localization.Away r)) ⟶
          Spec (.of (MvPolynomial (Fin d) K))),
        Etale q ∧
        q ≫ Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin d) K))) =
          Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away r))) ≫
            Spec.map (CommRingCat.ofHom (algebraMap K B)) ∧
        ∃ η : Spec (.of Ω) ⟶ Spec (.of (Localization.Away r)),
          η ≫ Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away r))) = ξ := by
  let : (ξ default).asIdeal.IsPrime := (ξ default).isPrime
  obtain ⟨r, hr, d, a, ht, he⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial
      (R := K) (p := (ξ default).asIdeal)
  let := a
  let := ht
  let := he
  let q := Spec.map (CommRingCat.ofHom
    (algebraMap (MvPolynomial (Fin d) K) (Localization.Away r)))
  have hq : Etale q :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      (RingHom.etale_algebraMap.mpr inferInstance)
  refine ⟨r, hr, d, q, hq, ?_, ?_⟩
  · change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq,
      ← IsScalarTower.algebraMap_eq]
  · exact EtaleChart.MarkedBaseChange.exists_mark_localizationAway ξ r hr

/-- The actual affine presentation and principal localization give a pointed
open chart of the original smooth object; no new marking is substituted. -/
theorem exists_smooth_site_marked_polynomial_chart
    (K Ω : Type u) [Field K] [Field Ω]
    (X : SmoothSite (Spec (.of K))) [IsAffine X.left]
    (ξ : Spec (.of Ω) ⟶ X.left) :
    ∃ (R : CommRingCat.{u}) (j : Spec R ⟶ X.left), IsOpenImmersion j ∧
      ∃ (d : ℕ) (q : Spec R ⟶ Spec (.of (MvPolynomial (Fin d) K))),
        Etale q ∧
        q ≫ Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin d) K))) =
          j ≫ X.hom ∧
        ∃ η : Spec (.of Ω) ⟶ Spec R, η ≫ j = ξ := by
  let B := Γ(X.left, ⊤)
  let i : Spec B ≅ X.left := X.left.isoSpec.symm
  let f : Spec B ⟶ Spec (.of K) := i.hom ≫ X.hom
  let φ := (Scheme.Spec.preimage f).unop.hom
  have hφ : Spec.map (CommRingCat.ofHom φ) = f := Scheme.Spec.map_preimage f
  let : Algebra K B := φ.toAlgebra
  let : Algebra.Smooth K B := by
    apply RingHom.smooth_algebraMap.mp
    apply (HasRingHomProperty.Spec_iff (P := @Smooth)).mp
    change Smooth (Spec.map (CommRingCat.ofHom φ))
    rw [hφ]
    exact inferInstanceAs (Smooth (i.hom ≫ X.hom))
  let ξB := ξ ≫ i.inv
  obtain ⟨r, hr, d, q, hq, hstruct, η, hη⟩ :=
    exists_smooth_affine_marked_polynomial_chart K B Ω ξB
  let k := Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away r)))
  refine ⟨.of (Localization.Away r), k ≫ i.hom, inferInstance, d, q, hq, ?_, η, ?_⟩
  · change q ≫ _ = k ≫ i.hom ≫ X.hom
    rw [hstruct]
    change k ≫ Spec.map (CommRingCat.ofHom φ) = _
    rw [hφ]
  · rw [← Category.assoc, hη]
    change (ξ ≫ i.inv) ≫ i.hom = ξ
    simp

end AlgebraicGeometry.Scheme.SmoothSite
