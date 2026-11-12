/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.CommonBoundaryCoordinates
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.SectionUnitRatio
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.CorrectionBoundaryMaps

/-!
# A norm quotient with prescribed values on two boundaries

Equality of the source norm and target coefficient on each entire
boundary gives a quotient with value one on their coproduct.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Ample Stacks.Divisors Stacks.Morphisms

universe u

namespace AlgebraicGeometry.Scheme

/-- The second projection of the actual pullback inherits finite local freeness. -/
theorem isFiniteLocallyFree_pullback_snd {X Y T : Scheme.{u}}
    (f : X ⟶ T) (v : Y ⟶ T) (hf : IsFiniteLocallyFree f) :
    IsFiniteLocallyFree (pullback.snd f v) :=
  isFiniteLocallyFree_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback f v) hf

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase

/-- A section equal to one on the full inverse boundary has norm one there. -/
theorem normTop_appTop_eq_one_of_boundary {X Y B : Scheme.{u}} (F : X ⟶ Y)
    (U : Y.Opens) (m : B ⟶ Y) (l : B ⟶ U.toScheme) (hl : l ≫ U.ι = m)
    (hF : IsFiniteLocallyFree F) (hG : IsFiniteLocallyFree (pullback.snd F U.ι))
    (r : Γ((pullback F U.ι : Scheme.{u}), ⊤))
    (hr : (normQuotientBoundaryMap F U m l hl).appTop r = 1) :
    l.appTop ((@normTop _ _ (pullback.snd F U.ι) hG) r) = 1 := by
  let : IsFiniteLocallyFree (pullback.snd F U.ι) := hG
  let : IsFiniteLocallyFree (pullback.snd F m) := isFiniteLocallyFree_pullback_snd F m hF
  rw [← normTop_appTop_of_isPullback (pullback.snd F U.ι) (pullback.snd F m)
    (normQuotientBoundaryMap F U m l hl) l (normQuotientBoundaryMap_isPullback F U m l hl),
    hr, map_one]

/-- The actual ratio is a unit with value one on the prescribed coproduct. -/
abbrev NormQuotientOnBoundaries {X Y B₁ B₂ : Scheme.{u}} (U : Y.Opens)
    (g : X ⟶ U.toScheme) [IsFiniteLocallyFree g] (m₁ : B₁ ⟶ Y) (m₂ : B₂ ⟶ Y)
    (cN : Γ(X, ⊤)) (cA : Γ(U.toScheme, ⊤)) : Prop :=
  ∃ (r : Γ(Y, U)) (l : B₁ ⨿ B₂ ⟶ U.toScheme),
    IsUnit r ∧ l ≫ U.ι = coprod.desc m₁ m₂ ∧ l.appTop (U.topIso.inv r) = 1 ∧
      normTop g cN * U.topIso.inv r = cA

/-- The quotient formed from two generating section pairs on their actual pullbacks. -/
abbrev NormQuotientOfSectionPairs {X Y X₀ Y₀ B₁ B₂ : Scheme.{u}} (U : Y.Opens)
    (g : X ⟶ U.toScheme) [IsFiniteLocallyFree g] (u₁ : X ⟶ X₀) (u₂ : U.toScheme ⟶ Y₀)
    (L : X₀.Modules) [hL : IsInvertibleModule X₀ L]
    (M : Y₀.Modules) [hM : IsInvertibleModule Y₀ M]
    (n d : Γ(L, ⊤)) (p a : Γ(M, ⊤)) (m₁ : B₁ ⟶ Y) (m₂ : B₂ ⟶ Y) : Prop :=
  ∃ (hn : @sectionGeneratesOnPullback X X₀ u₁ L hL n)
    (_hd : @sectionGeneratesOnPullback X X₀ u₁ L hL d)
    (hp : @sectionGeneratesOnPullback U.toScheme Y₀ u₂ M hM p)
    (_ha : @sectionGeneratesOnPullback U.toScheme Y₀ u₂ M hM a),
    NormQuotientOnBoundaries U g m₁ m₂
      (@sectionRatioCoefficientOnPullback X X₀ u₁ L hL n d hn)
      (@sectionRatioCoefficientOnPullback U.toScheme Y₀ u₂ M hM p a hp)

/-- Two generating sections have a unit coefficient in the pulled frame. -/
theorem isUnit_sectionRatioCoefficientOnPullback {W X : Scheme.{u}}
    (g : W ⟶ X) (L : X.Modules) [hL : IsInvertibleModule X L] (n d : Γ(L, ⊤))
    (hn : sectionGeneratesOnPullback g L n) (hd : sectionGeneratesOnPullback g L d) :
    IsUnit (sectionRatioCoefficientOnPullback g L n d hn) :=
  @isUnit_sectionRatioCoefficient_of_generates W ((Modules.pullback g).obj L)
    (@Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback W X g L hL)
    (pullbackGlobalSections g L n) (pullbackGlobalSections g L d) hn hd

/-- The common open carries the norm quotient when the actual coefficients
agree after restriction to the two prescribed boundaries. -/
theorem exists_normQuotient_on_boundaries {X Y B₁ B₂ : Scheme.{u}} (U : Y.Opens)
    (g : X ⟶ U.toScheme) [IsFiniteLocallyFree g] (m₁ : B₁ ⟶ Y) (m₂ : B₂ ⟶ Y)
    (hm₁ : Set.range m₁ ⊆ (U : Set Y)) (hm₂ : Set.range m₂ ⊆ (U : Set Y))
    (cN : Γ(X, ⊤)) (cA : Γ(U.toScheme, ⊤)) (hN : IsUnit cN) (hA : IsUnit cA)
    (h₁ : ∀ l : B₁ ⟶ U.toScheme, l ≫ U.ι = m₁ →
      l.appTop (normTop g cN) = l.appTop cA)
    (h₂ : ∀ l : B₂ ⟶ U.toScheme, l ≫ U.ι = m₂ →
      l.appTop (normTop g cN) = l.appTop cA) :
    NormQuotientOnBoundaries U g m₁ m₂ cN cA := by
  obtain ⟨r, hr, he, hboundary⟩ := exists_normQuotient_unit_on_open U g cN cA hN hA
  let l₁ := IsOpenImmersion.lift U.ι m₁ (by simpa only [Opens.range_ι] using hm₁)
  let l₂ := IsOpenImmersion.lift U.ι m₂ (by simpa only [Opens.range_ι] using hm₂)
  have hl₁ : l₁ ≫ U.ι = m₁ := IsOpenImmersion.lift_fac _ _ _
  have hl₂ : l₂ ≫ U.ι = m₂ := IsOpenImmersion.lift_fac _ _ _
  have hOne₁ : l₁.appTop (U.topIso.inv r) = 1 := hboundary l₁ (h₁ l₁ hl₁)
  have hOne₂ : l₂.appTop (U.topIso.inv r) = 1 := hboundary l₂ (h₂ l₂ hl₂)
  let l := coprod.desc l₁ l₂
  have hl : l ≫ U.ι = coprod.desc m₁ m₂ := by
    apply coprod.hom_ext <;>
      simp only [l, coprod.inl_desc_assoc, coprod.inr_desc_assoc, coprod.inl_desc,
        coprod.inr_desc, hl₁, hl₂]
  refine ⟨r, l, hr, hl, ?_, he⟩
  apply globalSections_coprod_ext
  · rw [← CommRingCat.comp_apply, ← Hom.comp_appTop]
    simpa only [l, coprod.inl_desc, map_one] using hOne₁
  · rw [← CommRingCat.comp_apply, ← Hom.comp_appTop]
    simpa only [l, coprod.inr_desc, map_one] using hOne₂

end AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase

end
