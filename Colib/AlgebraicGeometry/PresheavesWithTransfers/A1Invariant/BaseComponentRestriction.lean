/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.BaseComponentRetainedTargetMap
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.BaseComponentRetainedGeometry
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.BaseComponentFullBoundary
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.OriginalRootBaseComponentTransportResult
public import Colib.AlgebraicGeometry.Divisors.SectionKernelCartierPullback
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1Invariant.BoundaryFramedSectionActionNative

/-! # Restriction along the original maps after the same base and component refinement

The two retained sections and target map are constructed on literal pullbacks.
The original root and auxiliary pair are transported twice, without new choices.
Surjectivity is required only for the actual final full-boundary structure map.
-/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.SmoothSite
open AlgebraicGeometry.Scheme.Modules Stacks.Divisors
open Stacks.SheafOfModules.Invertible Stacks.AlgebraicGeometry.ModuleLimits
universe u v
set_option backward.isDefEq.respectTransparency false
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose Scheme.Modules
namespace AlgebraicGeometry.PresheafWithTransfers

local instance componentActionAG (X : Scheme.{u}) (M : X.Modules)
    [h : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property M :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ h

local instance componentActionPB {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    [Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatIsSheaf M] :
    Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf
      ((pullback f).obj M) :=
  Stacks.PullbackMonoidalSheaf.isInvertible_pullbackFunctor_obj f.toLRSHom.toShHom M

/-- The original two smooth-site maps agree on restrictions after the actual
closed base refinement and chosen normal component, using the same root and pair. -/
theorem restriction_baseComponent_same_root
    {K : Type u} [Field K] (P : PresheafWithTransfers.{v} K) (hP : IsA1Invariant P)
    {A Anew T : SmoothSite (Spec (.of K))}
    [IsAffine Anew.left] [IsIntegral Anew.left]
    (v : Anew ⟶ A) [IsOpenImmersion v.left] [IsClosedImmersion v.left]
    {X Y B : Scheme.{u}} (q : X ⟶ A.left) [IsProper q]
    [IsNormal (Limits.pullback q v.left)] [IsNoetherian (Limits.pullback q v.left)]
    (j : Y ⟶ X) [IsAffine Y] [IsOpenImmersion j]
    [SmoothOfRelativeDimension 1 (j ≫ q)]
    (d : B ⟶ X) (hd : Set.range d = (Set.range j)ᶜ)
    (σ τ : A.left ⟶ X) [IsClosedImmersion σ] [IsClosedImmersion τ]
    [IsEffectiveCartierDivisor σ.ker] [IsEffectiveCartierDivisor τ.ker]
    (hσ : σ ≫ q = 𝟙 _) (hτ : τ ≫ q = 𝟙 _)
    (σY τY : A.left ⟶ Y) (hσY : σY ≫ j = σ) (hτY : τY ≫ j = τ)
    (x : (Limits.pullback q v.left : Scheme.{u}))
    (σ₂ τ₂ : Anew.left ⟶ (normalComponentOpen x).toScheme)
    (hσ₂ : σ₂ ≫ (normalComponentOpen x).ι = baseChangedSection q v.left σ hσ)
    (hτ₂ : τ₂ ≫ (normalComponentOpen x).ι = baseChangedSection q v.left τ hτ)
    [Surjective (Limits.pullback.fst (normalComponentOpen x).ι
      (Limits.pullback.fst (Limits.pullback.fst q v.left) d) ≫
      (normalComponentOpen x).ι ≫ Limits.pullback.snd q v.left)]
    (r : Y ⟶ Limits.pullback A.hom T.hom)
    (hr : r ≫ Limits.pullback.fst A.hom T.hom = j ≫ q)
    (f g : A ⟶ T)
    (hf : f.left = σY ≫ r ≫ Limits.pullback.snd A.hom T.hom)
    (hg : g.left = τY ≫ r ≫ Limits.pullback.snd A.hom T.hom)
    (aD : ∀ z : B, d z ∉ σ.ker.support) (aE : ∀ z : B, d z ∉ τ.ker.support)
    (M N : X.Modules)
    [hM : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M]
    [Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf N]
    (k : ℕ) (hn : ∀ z : sections P ((Cor.graphFunctor K).obj Anew), (k + 1) • z = 0)
    (α : Stacks.SheafOfModules.schemeTensorPower X M hM ((k + 1 : ℕ) : ℤ) ≅
      differenceSheaf σ.ker τ.ker)
    (e : (pullback d).obj M ≅ SheafOfModules.unit B.ringCatSheaf)
    (eN : (pullback d).obj N ≅ SheafOfModules.unit B.ringCatSheaf)
    (a : Γ(((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj M).obj N, ⊤)) (bN : Γ(N, ⊤))
    (he : tensorPowerCongr B.presheaf (ringSheafCond B) _ _ e (k + 1) =
      boundaryRootPowerIso d M _ (k + 1) α (differenceSheafBoundaryIso d σ.ker τ.ker aD aE))
    (ha : Hom.app (pullbackTensorFrame d M N e eN).hom ⊤
      (pullbackGlobalSections d _ a) = (1 : Γ(B, ⊤)))
    (hb : Hom.app eN.hom ⊤ (pullbackGlobalSections d N bN) = (1 : Γ(B, ⊤))) :
    ((toPresheaf K).obj P).map (v ≫ f).op = ((toPresheaf K).obj P).map (v ≫ g).op := by
  let F := Limits.pullback.fst q v.left
  let q₁ := Limits.pullback.snd q v.left
  let κ := (normalComponentOpen x).ι
  let q₂ := κ ≫ q₁
  let j₁ := Limits.pullback.fst F j
  let j₂ := Limits.pullback.fst κ j₁
  let i₁ := Limits.pullback.fst F d
  let b₁ := Limits.pullback.snd F d
  let i₂ := Limits.pullback.fst κ i₁
  let b₂ := Limits.pullback.snd κ i₁
  have w₁ : b₁ ≫ d = i₁ ≫ F := (Limits.pullback.condition (f := F) (g := d)).symm
  have w₂ : b₂ ≫ i₁ = i₂ ≫ κ := (Limits.pullback.condition (f := κ) (g := i₁)).symm
  let σ₁ := baseChangedSection q v.left σ hσ
  let τ₁ := baseChangedSection q v.left τ hτ
  have hs₁ := isPullback_baseChangedSection q v.left σ hσ
  have ht₁ := isPullback_baseChangedSection q v.left τ hτ
  let : IsClosedImmersion σ₁ :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) hs₁.flip inferInstance
  let : IsClosedImmersion τ₁ :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) ht₁.flip inferInstance
  let : IsEffectiveCartierDivisor σ₁.ker :=
    isEffectiveCartierDivisor_ker_cartesian_of_flat F v.left σ σ₁ hs₁
  let : IsEffectiveCartierDivisor τ₁.ker :=
    isEffectiveCartierDivisor_ker_cartesian_of_flat F v.left τ τ₁ ht₁
  have hσq : σ₂ ≫ q₂ = 𝟙 _ := by
    simpa only [q₂, ← Category.assoc, hσ₂] using baseChangedSection_snd q v.left σ hσ
  have hτq : τ₂ ≫ q₂ = 𝟙 _ := by
    simpa only [q₂, ← Category.assoc, hτ₂] using baseChangedSection_snd q v.left τ hτ
  obtain ⟨σRet, hσRet, hfFinal⟩ := exists_baseComponentRetained_section_originalTarget
    v q j κ r hr σ hσ σY hσY σ₂ hσ₂ f hf
  obtain ⟨τRet, hτRet, hgFinal⟩ := exists_baseComponentRetained_section_originalTarget
    v q j κ r hr τ hτ τY hτY τ₂ hτ₂ g hg
  let z : Anew.left := Classical.choice (inferInstance : Nonempty Anew.left)
  obtain ⟨hAff, hInt, hNoeth, hDom⟩ :=
    baseComponent_retained_geometry_of_section F j x σRet z
  let := hAff
  let := hInt
  let := hNoeth
  let := hDom
  let : IsNoetherian (normalComponentOpen x).toScheme :=
    PrincipalFamilyUnitOpen.retainedCurve_isNoetherian κ
  let : Nonempty (Limits.pullback κ i₁ : Scheme.{u}) := by
    obtain ⟨b, _⟩ := (i₂ ≫ κ ≫ q₁).surjective z
    exact ⟨b⟩
  let : SmoothOfRelativeDimension 1 (j₁ ≫ q₁) :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension 1)
      ((IsPullback.of_hasPullback F j).flip.paste_vert
        (IsPullback.of_hasPullback q v.left)) inferInstance
  let : SmoothOfRelativeDimension 1 (j₂ ≫ q₂) :=
    smoothOfRelativeDimension_normalComponentOpen q₁ j₁ 1 x
  let : IsEffectiveCartierDivisor σ₂.ker :=
    sectionKernel_cartier_of_factor q₂ j₂ σ₂ hσq σRet hσRet
  let : IsEffectiveCartierDivisor τ₂.ker :=
    sectionKernel_cartier_of_factor q₂ j₂ τ₂ hτq τRet hτRet
  have hcover : ∀ y : (normalComponentOpen x).toScheme,
      y ∈ Set.range j₂ ∨ y ∈ Set.range i₂ := by
    intro y
    by_cases hy : y ∈ Set.range j₂
    · exact Or.inl hy
    · exact Or.inr (by
        rw [show Set.range i₂ = (Set.range j₂)ᶜ from
          range_baseComponent_fullBoundary F j d hd x]
        exact hy)
  let aD₁ := avoids_sectionKernel_cartesianSections b₁ d i₁ F v.left w₁ σ σ₁ hs₁ aD
  let aE₁ := avoids_sectionKernel_cartesianSections b₁ d i₁ F v.left w₁ τ τ₁ ht₁ aE
  let aD₂ := avoids_sectionKernel_openRestriction b₂ i₁ i₂ κ w₂ σ₁ σ₂ hσ₂ aD₁
  let aE₂ := avoids_sectionKernel_openRestriction b₂ i₁ i₂ κ w₂ τ₁ τ₂ hτ₂ aE₁
  let M₁ := (pullback F).obj M
  let N₁ := (pullback F).obj N
  let M₂ := (pullback κ).obj M₁
  let N₂ := (pullback κ).obj N₁
  let α₁ := ((pullbackTensorPowerIso F M (k + 1)).symm ≪≫ (pullback F).mapIso α) ≪≫
    sectionKernelDifferenceOfCartesianSectionsIso F v.left σ τ σ₁ τ₁ hs₁ ht₁
  let α₂ := ((pullbackTensorPowerIso κ M₁ (k + 1)).symm ≪≫ (pullback κ).mapIso α₁) ≪≫
    sectionKernelDifferenceOpenRestrictionIso κ σ₁ τ₁ σ₂ τ₂ hσ₂ hτ₂
  let e₁ := pullbackBoundaryTrivialization b₁ d i₁ F w₁ M e
  let eN₁ := pullbackBoundaryTrivialization b₁ d i₁ F w₁ N eN
  let e₂ := pullbackBoundaryTrivialization b₂ i₁ i₂ κ w₂ M₁ e₁
  let eN₂ := pullbackBoundaryTrivialization b₂ i₁ i₂ κ w₂ N₁ eN₁
  let a₁ := Hom.app (pullbackTensorIso F M N).hom ⊤ (pullbackGlobalSections F _ a)
  let a₂ := Hom.app (pullbackTensorIso κ M₁ N₁).hom ⊤ (pullbackGlobalSections κ _ a₁)
  let b₂N := pullbackGlobalSections κ N₁ (pullbackGlobalSections F N bN)
  have hTransport := originalRootBaseComponentTransportResult
    F κ v.left b₁ b₂ d i₁ i₂ w₁ w₂ σ τ σ₁ τ₁ σ₂ τ₂
    hs₁ ht₁ hσ₂ hτ₂ aD aE M (k + 1) α e he N eN a bN ha hb
  have hRoot := hTransport.1
  have hPair := hTransport.2
  let rFinal := baseComponentRetainedTargetMap v q j κ r hr
  have hrFinal : rFinal ≫ Limits.pullback.fst Anew.hom T.hom = j₂ ≫ q₂ :=
    baseComponentRetainedTargetMap_fst v q j κ r hr
  have hAction := restriction_boundary_framed_section_pair_eq_native P hP Anew T
    q₂ i₂ j₂ hcover rFinal hrFinal σ₂ τ₂ hσq hτq σRet τRet hσRet hτRet
    aD₂ aE₂ M₂ N₂ k hn α₂ e₂ eN₂ a₂ b₂N hPair.1 hPair.2
    (v ≫ f) (v ≫ g) hfFinal hgFinal
  exact hAction hRoot

end AlgebraicGeometry.PresheafWithTransfers
