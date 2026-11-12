/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.Quadratic.RetainedEtaleSmoothSite
public import Mathlib.RingTheory.Etale.Field

/-! # Finite separable quadratic charts over the original ground field -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme

/-- The original finite-stage polynomial coordinate space is smooth over K,
not merely over its finite separable coefficient field E. -/
instance finiteSeparableMvPolynomialStructure_smooth
    (K E : Type u) [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [Algebra.IsSeparable K E] (d : ℕ) :
    Smooth (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin d) E)))) := by
  let : Algebra.FormallyEtale K E := Algebra.FormallyEtale.of_isSeparable K E
  let : Algebra.FinitePresentation K E :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let : Algebra.Smooth K E := {}
  let : Algebra.Smooth E (MvPolynomial (Fin d) E) := {}
  let : Algebra.Smooth K (MvPolynomial (Fin d) E) :=
    Algebra.Smooth.comp K E (MvPolynomial (Fin d) E)
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  exact RingHom.smooth_algebraMap.mpr inferInstance

/-- The same literal structure map is separated and quasi-compact because it
is a morphism between affine schemes. -/
theorem finiteSeparableMvPolynomialStructure_finiteTypeSite
    (K E : Type u) [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [Algebra.IsSeparable K E] (d : ℕ) :
    let y := Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin d) E)))
    Smooth y ∧ IsSeparated y ∧ QuasiCompact y :=
  ⟨inferInstance, inferInstance, inferInstance⟩

/-- Apply the actual rational marked-intersection producer without changing the
base S, the tuple, either open, or the chosen coordinate-value section. In the
application S is Spec K, while E is the finite-stage marking field. -/
theorem exists_finiteSeparable_quadraticRetainedEtaleChart_smoothSite
    (K E : Type u) [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [Algebra.IsSeparable K E]
    (d : ℕ) {B : Type u} [CommRing B] [Algebra E B]
    (f : Polynomial (MvPolynomial (Fin d) E) →ₐ[E] B) (x : Spec (.of E) ⟶ Spec (.of B))
    (hx : x ≫ Spec.map (CommRingCat.ofHom (algebraMap E B)) = 𝟙 _)
    (re r : B) (hre : re ∉ (x default).asIdeal) (hr : r ∉ (x default).asIdeal)
    (he : ((algebraMap B (Localization.Away re)).comp f.toRingHom).Etale) :
    let je := Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away re)))
    let jr := Scheme.Opens.ι (X := Spec (.of B)) (PrimeSpectrum.basicOpen r)
    let q := pullback.fst je jr ≫ je ≫ Spec.map (CommRingCat.ofHom f.toRingHom)
    let p := Spec.map (CommRingCat.ofHom
      (Polynomial.C : MvPolynomial (Fin d) E →+* Polynomial (MvPolynomial (Fin d) E)))
    ∃ (hq : Etale q) (hp : Smooth p)
      (s : Spec (.of (MvPolynomial (Fin d) E)) ⟶
        Spec (.of (Polynomial (MvPolynomial (Fin d) E)))) (hs : s ≫ p = 𝟙 _)
      (η : Spec (.of E) ⟶ Spec (.of (MvPolynomial (Fin d) E)))
      (ξ : Spec (.of E) ⟶ quadraticRetainedEtaleChart re r),
      let Y := SmoothSite.mk (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin d) E))))
      let hY : IsAffine Y.left := inferInstanceAs (IsAffine (Spec (.of (MvPolynomial (Fin d) E))))
      let hA : IsAffine (quadraticRetainedEtaleChart re r) :=
        quadraticRetainedEtaleChart_isAffine re r
      let hZ : IsAffine (Spec (.of (Polynomial (MvPolynomial (Fin d) E)))) := inferInstance
      let qs := @SmoothSite.EtaleChart.chart (Spec (.of K)) Y hY
        (quadraticRetainedEtaleChart re r) (Spec (.of (Polynomial (MvPolynomial (Fin d) E))))
        hA hZ p hp q hq
      let ps := @SmoothSite.EtaleChart.projection (Spec (.of K)) Y hY
        (Spec (.of (Polynomial (MvPolynomial (Fin d) E)))) hZ p hp
      let ss := @SmoothSite.EtaleChart.sectionMap (Spec (.of K)) Y hY
        (Spec (.of (Polynomial (MvPolynomial (Fin d) E)))) hZ p hp s hs
      ss ≫ ps = 𝟙 Y ∧ ξ ≫ qs.left = η ≫ ss.left ∧
        ξ ≫ pullback.snd je jr ≫ jr = x := by
  exact exists_quadraticRetainedEtaleChart_smoothSite
    (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin d) E))))
    f x hx re r hre hr he

end AlgebraicGeometry.Scheme
