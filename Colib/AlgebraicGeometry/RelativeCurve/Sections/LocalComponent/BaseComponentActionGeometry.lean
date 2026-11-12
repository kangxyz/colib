/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.BaseComponentRetainedGeometry
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.BaseComponentFullBoundary
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.BaseChangedMarkedComponentSections
public import Colib.AlgebraicGeometry.Divisors.SectionKernelCartierPullback
public import Colib.AlgebraicGeometry.Divisors.SectionKernelOpenRestriction

/-! # Actual geometry for the terminal component action

These lemmas separate native geometric constructions from root and frame
elaboration. They use only the actual pullback and normal component objects.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Stacks.Divisors
universe u
set_option backward.isDefEq.respectTransparency false
namespace AlgebraicGeometry.Scheme

/-- The same original section retains its section law and actual Cartier kernel
through base change and the chosen open component. -/
theorem baseComponent_action_section_geometry
    {A Anew X : Scheme.{u}} (q : X ⟶ A) (g : Anew ⟶ A) [IsOpenImmersion g]
    [IsNormal (pullback q g)] [IsNoetherian (pullback q g)]
    (σ : A ⟶ X) [IsClosedImmersion σ] [IsEffectiveCartierDivisor σ.ker]
    (hσ : σ ≫ q = 𝟙 A) (x : (pullback q g : Scheme.{u}))
    (σ₂ : Anew ⟶ (normalComponentOpen x).toScheme)
    (hσ₂ : σ₂ ≫ (normalComponentOpen x).ι = baseChangedSection q g σ hσ) :
    IsClosedImmersion (baseChangedSection q g σ hσ) ∧
    IsEffectiveCartierDivisor (baseChangedSection q g σ hσ).ker ∧
    IsEffectiveCartierDivisor σ₂.ker ∧
    σ₂ ≫ (normalComponentOpen x).ι ≫ pullback.snd q g = 𝟙 Anew := by
  let F := pullback.fst q g
  let κ := (normalComponentOpen x).ι
  let σ₁ := baseChangedSection q g σ hσ
  have hs₁ := isPullback_baseChangedSection q g σ hσ
  let hClosed : IsClosedImmersion σ₁ :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) hs₁.flip inferInstance
  let hCartier : IsEffectiveCartierDivisor σ₁.ker :=
    isEffectiveCartierDivisor_ker_cartesian_of_flat F g σ σ₁ hs₁
  have hCartier₂ : IsEffectiveCartierDivisor σ₂.ker :=
    isEffectiveCartierDivisor_ker_cartesian_of_flat κ (𝟙 Anew) σ₁ σ₂
      (isPullback_section_openRestriction κ σ₁ σ₂ hσ₂)
  refine ⟨hClosed, hCartier, hCartier₂, ?_⟩
  calc
    σ₂ ≫ κ ≫ pullback.snd q g = (σ₂ ≫ κ) ≫ pullback.snd q g :=
      (Category.assoc _ _ _).symm
    _ = baseChangedSection q g σ hσ ≫ pullback.snd q g :=
      congrArg (fun t => t ≫ pullback.snd q g) hσ₂
    _ = 𝟙 _ := baseChangedSection_snd q g σ hσ

/-- The literal twice-retained open and full boundary have all terminal action
geometry. A genuine retained section supplies nonemptiness of the open; actual
boundary surjectivity separately supplies nonemptiness of the full boundary. -/
theorem baseComponent_retained_action_geometry
    {A Anew X Y B : Scheme.{u}} (q : X ⟶ A) (g : Anew ⟶ A)
    [IsClosedImmersion g] [IsNormal (pullback q g)] [IsNoetherian (pullback q g)]
    (j : Y ⟶ X) [IsAffine Y] [IsOpenImmersion j]
    [SmoothOfRelativeDimension 1 (j ≫ q)]
    (d : B ⟶ X) (hd : Set.range d = (Set.range j)ᶜ)
    (x : (pullback q g : Scheme.{u}))
    [Surjective (pullback.fst (normalComponentOpen x).ι
      (pullback.fst (pullback.fst q g) d) ≫
      (normalComponentOpen x).ι ≫ pullback.snd q g)]
    (σRet : Anew ⟶ pullback (normalComponentOpen x).ι
      (pullback.fst (pullback.fst q g) j)) (z : Anew) :
    let κ := (normalComponentOpen x).ι
    let j₁ := pullback.fst (pullback.fst q g) j
    let i₁ := pullback.fst (pullback.fst q g) d
    IsAffine (pullback κ j₁) ∧ IsIntegral (pullback κ j₁) ∧
    IsNoetherian (pullback κ j₁) ∧ IsDominant (pullback.fst κ j₁) ∧
    IsNoetherian (normalComponentOpen x).toScheme ∧
    Nonempty (pullback κ i₁ : Scheme.{u}) ∧
    SmoothOfRelativeDimension 1 (pullback.fst κ j₁ ≫ κ ≫ pullback.snd q g) ∧
    ∀ y : (normalComponentOpen x).toScheme,
      y ∈ Set.range (pullback.fst κ j₁) ∨ y ∈ Set.range (pullback.fst κ i₁) := by
  let F := pullback.fst q g
  let κ := (normalComponentOpen x).ι
  let j₁ := pullback.fst F j
  let i₁ := pullback.fst F d
  obtain ⟨hAff, hInt, hNoeth, hDom⟩ :=
    baseComponent_retained_geometry_of_section F j x σRet z
  have hComp : IsNoetherian (normalComponentOpen x).toScheme :=
    PrincipalFamilyUnitOpen.retainedCurve_isNoetherian κ
  have hBoundary : Nonempty (pullback κ i₁ : Scheme.{u}) := by
    obtain ⟨b, _⟩ := (pullback.fst κ i₁ ≫ κ ≫ pullback.snd q g).surjective z
    exact ⟨b⟩
  let : SmoothOfRelativeDimension 1 (j₁ ≫ pullback.snd q g) :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension 1)
      ((IsPullback.of_hasPullback F j).flip.paste_vert
        (IsPullback.of_hasPullback q g)) inferInstance
  have hSmooth : SmoothOfRelativeDimension 1
      (pullback.fst κ j₁ ≫ κ ≫ pullback.snd q g) :=
    smoothOfRelativeDimension_normalComponentOpen (pullback.snd q g) j₁ 1 x
  refine ⟨hAff, hInt, hNoeth, hDom, hComp, hBoundary, hSmooth, ?_⟩
  intro y
  by_cases hy : y ∈ Set.range (pullback.fst κ j₁)
  · exact Or.inl hy
  · exact Or.inr (by
      rw [range_baseComponent_fullBoundary F j d hd x]
      exact hy)

end AlgebraicGeometry.Scheme
