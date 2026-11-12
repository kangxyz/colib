/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.Basic
public import Colib.AlgebraicGeometry.Scheme.AffinePullbackSections
public import Colib.RingTheory.Polynomial.GenericFreeness
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.TensorProduct.Free
public import StacksFrontier.Algebra.Module.TorsionFree
import Mathlib.Tactic.FinCases

/-!
# Freeness on an actual polynomial chart of the relative normalization

On an affine chart, sections of the finite normalization inject into
sections of the original étale source. The latter are flat over the chart.
The normalization is therefore torsion-free, and its chart becomes
finite free after a nonzero coefficient localization.

Adapted from the chart freeness result in
`Motivic/Aglib/AlgebraicGeometry/Normalization/FiniteCurve/PolynomialChartFiniteFlat.lean`
at a6805c4a87cdfd7717dd7a94039246a167f15380, using the actual relative normalization.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Polynomial TensorProduct nonZeroDivisors

attribute [local instance] Polynomial.algebra

universe u

namespace AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  {Y : Scheme.{u}} [IsAffine Y] (p : Y ⟶ Spec (.of R[X]))
  [Etale p] [QuasiCompact p] [IsFinite (toProjectiveLine R p)]
  (c : Spec (.of R[X]) ⟶ projectiveSpaceOverRing 1 (.of R)) [IsOpenImmersion c]

omit [IsDomain R] in
/-- The actual chart section ring of the normalization is torsion-free over its
polynomial coordinates. -/
theorem polynomialChartSections_isTorsionFree :
    let q := pullback.snd (toProjectiveLine R p) c
    let : Algebra R[X] Γ(pullback (toProjectiveLine R p) c, ⊤) := (specSectionsMap q).toAlgebra
    Module.IsTorsionFree R[X] Γ(pullback (toProjectiveLine R p) c, ⊤) := by
  dsimp only
  let f := projectiveMap R p
  let b := (projectiveSpaceOverRing 1 (.of R) ↘ Spec (.of R))
  let : IsAffineHom (f ≫ b) := isAffineHom_of_isAffine (f ≫ b)
  let : IsAffineHom f := IsAffineHom.of_comp f b
  let q := pullback.snd f c
  let n := pullback.snd f.fromNormalization c
  let : IsAffine (pullback f c) := isAffine_of_isAffineHom q
  let : IsAffine (pullback f.fromNormalization c) := isAffine_of_isAffineHom n
  let m := q.toNormalization ≫ f.normalizationPullback c
  have hm : m ≫ n = q := by
    dsimp only [m, n, q]
    rw [Category.assoc, Scheme.Hom.normalizationPullback_snd,
      Scheme.Hom.toNormalization_fromNormalization]
  let : IsSchemeTheoreticallyDominant q.toNormalization := ⟨q.ker_toNormalization⟩
  let : IsSchemeTheoreticallyDominant m := by
    dsimp only [m]
    infer_instance
  let : IsAffineHom m := isAffineHom_of_isAffine m
  have hi : Function.Injective m.appTop.hom := m.app_injective ⊤
  let : Algebra R[X] Γ(pullback f c, ⊤) := (specSectionsMap q).toAlgebra
  let : Algebra R[X] Γ(pullback f.fromNormalization c, ⊤) := (specSectionsMap n).toAlgebra
  have : Module.Flat R[X] Γ(pullback f c, ⊤) := by
    have hf : Flat (Spec.map (CommRingCat.ofHom (specSectionsMap q))) := by
      rw [Spec_map_specSectionsMap q]
      infer_instance
    exact RingHom.flat_algebraMap_iff.mp (Flat.SpecMap_iff.mp hf)
  let φ : Γ(pullback f.fromNormalization c, ⊤) →ₐ[R[X]] Γ(pullback f c, ⊤) :=
    { m.appTop.hom with
      commutes' := fun a ↦ by
        change ((ΓSpecIso (.of R[X])).inv ≫ n.appTop ≫ m.appTop).hom a =
          ((ΓSpecIso (.of R[X])).inv ≫ q.appTop).hom a
        rw [← Scheme.Hom.comp_appTop, hm] }
  change Module.IsTorsionFree R[X] Γ(pullback f.fromNormalization c, ⊤)
  constructor
  intro a ha x y hxy
  apply hi
  change φ x = φ y
  exact (ha.isSMulRegular : IsSMulRegular Γ(pullback f c, ⊤) a)
    (by simpa only [map_smul] using congrArg φ hxy)

/-- A nonzero coefficient localization makes the actual whole normalization
chart free over the localized polynomial ring. -/
theorem exists_free_polynomial_chart_sections :
    ∃ r : R, r ≠ 0 ∧
      let A := (Localization.Away r)[X]
      let l := Spec.map (CommRingCat.ofHom (algebraMap R[X] A))
      let q := pullback.snd (toProjectiveLine R p) (l ≫ c)
      let : Algebra A Γ(pullback (toProjectiveLine R p) (l ≫ c), ⊤) := (specSectionsMap q).toAlgebra
      Module.Free A Γ(pullback (toProjectiveLine R p) (l ≫ c), ⊤) := by
  let f := toProjectiveLine R p
  let n := pullback.snd f c
  let T := Γ(pullback f c, ⊤)
  let : IsAffine (pullback f c) := isAffine_of_isAffineHom n
  let : Algebra R[X] T := (specSectionsMap n).toAlgebra
  let : Module.IsTorsionFree R[X] T := polynomialChartSections_isTorsionFree R p c
  have : Module.Finite R[X] T := by
    apply RingHom.finite_algebraMap.mp
    apply (IsFinite.SpecMap_iff (CommRingCat.ofHom (specSectionsMap n))).mp
    rw [Spec_map_specSectionsMap n]
    infer_instance
  let : Module.FinitePresentation R[X] T := Module.finitePresentation_of_finite R[X] T
  let K := FractionRing R
  let S : Submonoid R[X] := R⁰.map Polynomial.C
  let : IsLocalization S K[X] := Polynomial.isLocalization R⁰ K
  let : Module.IsTorsionFree K[X] (K[X] ⊗[R[X]] T) :=
    IsLocalizedModule.isTorsionFree (TensorProduct.mk R[X] K[X] T 1) S
  obtain ⟨r, hr, hfree⟩ := Module.exists_free_polynomial_tensorProduct_away R K T
  let A := (Localization.Away r)[X]
  let l := Spec.map (CommRingCat.ofHom (algebraMap R[X] A))
  let q := pullback.snd f (l ≫ c)
  let : Algebra A Γ(pullback f (l ≫ c), ⊤) := (specSectionsMap q).toAlgebra
  let : Module.Free A (A ⊗[R[X]] T) := hfree
  exact ⟨r, hr, Module.Free.of_equiv
    (affinePullbackSpecSectionsCompAlgEquiv f c (algebraMap R[X] A)).toLinearEquiv⟩

omit [IsDomain R] [IsAffine Y] [IsOpenImmersion c] in
private theorem free_polynomial_chart_sections_of_factor (s r : R)
    (φ : (Localization.Away s)[X] →+* (Localization.Away r)[X])
    (hφ : φ.comp (algebraMap R[X] (Localization.Away s)[X]) =
      algebraMap R[X] (Localization.Away r)[X])
    (hfree :
      let A := (Localization.Away s)[X]
      let l := Spec.map (CommRingCat.ofHom (algebraMap R[X] A))
      let q := pullback.snd (toProjectiveLine R p) (l ≫ c)
      let : Algebra A Γ(pullback (toProjectiveLine R p) (l ≫ c), ⊤) := (specSectionsMap q).toAlgebra
      Module.Free A Γ(pullback (toProjectiveLine R p) (l ≫ c), ⊤)) :
    let B := (Localization.Away r)[X]
    let l := Spec.map (CommRingCat.ofHom (algebraMap R[X] B))
    let q := pullback.snd (toProjectiveLine R p) (l ≫ c)
    let : Algebra B Γ(pullback (toProjectiveLine R p) (l ≫ c), ⊤) := (specSectionsMap q).toAlgebra
    Module.Free B Γ(pullback (toProjectiveLine R p) (l ≫ c), ⊤) := by
  dsimp only
  let A := (Localization.Away s)[X]
  let B := (Localization.Away r)[X]
  let f := toProjectiveLine R p
  let g := Spec.map (CommRingCat.ofHom (algebraMap R[X] A)) ≫ c
  let l := Spec.map (CommRingCat.ofHom φ)
  have hl : l ≫ g = Spec.map (CommRingCat.ofHom (algebraMap R[X] B)) ≫ c := by
    have hRing : (CommRingCat.ofHom (algebraMap R[X] A) ≫ CommRingCat.ofHom φ) =
        CommRingCat.ofHom (algebraMap R[X] B) :=
      CommRingCat.hom_ext hφ
    dsimp only [l, g]
    rw [← Category.assoc, ← Spec.map_comp, hRing]
  let : IsAffine (pullback f g) := isAffine_of_isAffineHom (pullback.snd f g)
  let : Algebra A B := φ.toAlgebra
  let : Algebra A Γ(pullback f g, ⊤) := (specSectionsMap (pullback.snd f g)).toAlgebra
  let : Module.Free A Γ(pullback f g, ⊤) := hfree
  let : Module.Free B (B ⊗[A] Γ(pullback f g, ⊤)) := inferInstance
  have hFree' :
      let : Algebra B Γ(pullback f (l ≫ g), ⊤) :=
        (specSectionsMap (pullback.snd f (l ≫ g))).toAlgebra
      Module.Free B Γ(pullback f (l ≫ g), ⊤) := by
    dsimp only
    let : Algebra B Γ(pullback f (l ≫ g), ⊤) :=
      (specSectionsMap (pullback.snd f (l ≫ g))).toAlgebra
    exact Module.Free.of_equiv (affinePullbackSpecSectionsCompAlgEquiv f g φ).toLinearEquiv
  let freeOver (g' : Spec (.of B) ⟶ projectiveSpaceOverRing 1 (.of R)) : Prop :=
    let : Algebra B Γ(pullback f g', ⊤) := (specSectionsMap (pullback.snd f g')).toAlgebra
    Module.Free B Γ(pullback f g', ⊤)
  change freeOver (Spec.map (CommRingCat.ofHom (algebraMap R[X] B)) ≫ c)
  exact (congrArg freeOver hl).mp hFree'

/-- The two polynomial charts of one normalization become free after a
single nonzero coefficient localization. -/
theorem exists_common_free_polynomial_chart_sections
    (charts : Fin 2 → (Spec (.of R[X]) ⟶ projectiveSpaceOverRing 1 (.of R)))
    [∀ i, IsOpenImmersion (charts i)] :
    ∃ r : R, r ≠ 0 ∧ ∀ i : Fin 2,
      let A := (Localization.Away r)[X]
      let l := Spec.map (CommRingCat.ofHom (algebraMap R[X] A))
      let q := pullback.snd (toProjectiveLine R p) (l ≫ charts i)
      let : Algebra A Γ(pullback (toProjectiveLine R p) (l ≫ charts i), ⊤) :=
        (specSectionsMap q).toAlgebra
      Module.Free A Γ(pullback (toProjectiveLine R p) (l ≫ charts i), ⊤) := by
  obtain ⟨s, hs, h₀⟩ := exists_free_polynomial_chart_sections R p (charts 0)
  obtain ⟨t, ht, h₁⟩ := exists_free_polynomial_chart_sections R p (charts 1)
  let B := Localization.Away (s * t)
  let φ₀ : Localization.Away s →+* B := IsLocalization.Away.awayToAwayRight s t
  let φ₁ : Localization.Away t →+* B := IsLocalization.Away.awayToAwayLeft t s
  refine ⟨s * t, mul_ne_zero hs ht, ?_⟩
  intro i
  fin_cases i
  · apply free_polynomial_chart_sections_of_factor R p (charts 0) s (s * t)
      (Polynomial.mapRingHom φ₀) ?_ h₀
    change (Polynomial.mapRingHom φ₀).comp (Polynomial.mapRingHom _) = Polynomial.mapRingHom _
    rw [Polynomial.mapRingHom_comp]
    congr 1
    ext a
    exact IsLocalization.Away.awayToAwayRight_eq s t a
  · apply free_polynomial_chart_sections_of_factor R p (charts 1) t (s * t)
      (Polynomial.mapRingHom φ₁) ?_ h₁
    change (Polynomial.mapRingHom φ₁).comp (Polynomial.mapRingHom _) = Polynomial.mapRingHom _
    rw [Polynomial.mapRingHom_comp]
    congr 1
    ext a
    exact IsLocalization.Away.awayToAwayLeft_eq t s a

end AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification
