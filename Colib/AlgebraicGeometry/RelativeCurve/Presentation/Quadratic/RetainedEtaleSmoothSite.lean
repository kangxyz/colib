/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.EtaleChartSmoothSite
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.Quadratic.RetainedEtaleChart

/-! # The actual quadratic intersection chart in the original smooth site -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme

/-- Apply the actual rational marked-intersection producer without changing the
base S, the tuple, either open, or the chosen coordinate-value section. In the
application S is Spec K, while E is the finite-stage marking field. -/
theorem exists_quadraticRetainedEtaleChart_smoothSite
    {S : Scheme.{u}} {E R B : Type u} [Field E] [CommRing R] [CommRing B]
    [Algebra E R] [Algebra E B]
    (y : Spec (.of R) ⟶ S) [Smooth y] [IsSeparated y] [QuasiCompact y]
    (f : Polynomial R →ₐ[E] B) (x : Spec (.of E) ⟶ Spec (.of B))
    (hx : x ≫ Spec.map (CommRingCat.ofHom (algebraMap E B)) = 𝟙 _)
    (re r : B) (hre : re ∉ (x default).asIdeal) (hr : r ∉ (x default).asIdeal)
    (he : ((algebraMap B (Localization.Away re)).comp f.toRingHom).Etale) :
    let je := Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away re)))
    let jr := Scheme.Opens.ι (X := Spec (.of B)) (PrimeSpectrum.basicOpen r)
    let q := pullback.fst je jr ≫ je ≫ Spec.map (CommRingCat.ofHom f.toRingHom)
    let p := Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))
    ∃ (hq : Etale q) (hp : Smooth p)
      (s : Spec (.of R) ⟶ Spec (.of (Polynomial R))) (hs : s ≫ p = 𝟙 _)
      (η : Spec (.of E) ⟶ Spec (.of R))
      (ξ : Spec (.of E) ⟶ quadraticRetainedEtaleChart re r),
      let Y := SmoothSite.mk y
      let hY : IsAffine Y.left := inferInstanceAs (IsAffine (Spec (.of R)))
      let hA : IsAffine (quadraticRetainedEtaleChart re r) :=
        quadraticRetainedEtaleChart_isAffine re r
      let hZ : IsAffine (Spec (.of (Polynomial R))) := inferInstance
      let qs := @SmoothSite.EtaleChart.chart S Y hY
        (quadraticRetainedEtaleChart re r) (Spec (.of (Polynomial R))) hA hZ p hp q hq
      let ps := @SmoothSite.EtaleChart.projection S Y hY
        (Spec (.of (Polynomial R))) hZ p hp
      let ss := @SmoothSite.EtaleChart.sectionMap S Y hY
        (Spec (.of (Polynomial R))) hZ p hp s hs
      ss ≫ ps = 𝟙 Y ∧ ξ ≫ qs.left = η ≫ ss.left ∧
        ξ ≫ pullback.snd je jr ≫ jr = x := by
  obtain ⟨hq, _, hp, _, s, η, ξ, hs, hξ, hx'⟩ :=
    exists_quadraticRetainedEtaleChart_data f x hx re r hre hr he
  refine ⟨hq, @SmoothOfRelativeDimension.smooth 1 _ _ _ hp, s, hs, η, ξ, ?_⟩
  exact ⟨MorphismProperty.Over.Hom.ext hs, hξ, hx'⟩

end AlgebraicGeometry.Scheme
