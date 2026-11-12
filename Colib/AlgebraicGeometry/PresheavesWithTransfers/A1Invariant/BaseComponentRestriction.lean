/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.BaseComponentActionGeometry
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.BaseComponentRetainedTargetMap
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.BaseComponentRetainedGeometry
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.BaseComponentFullBoundary
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.OriginalRootBaseComponentTransportResult
public import Colib.AlgebraicGeometry.Divisors.SectionKernelCartierPullback
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1Invariant.BoundaryFramedSectionActionNative

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1Invariant.BaseComponentTransportAction

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

local instance componentActionUnit (B : Scheme.{u}) :
    AlgebraicGeometry.SheafOfModules.IsInvertible B.presheaf (ringSheafCond B)
      (SheafOfModules.unit B.ringCatSheaf) :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (Stacks.SheafOfModules.isInvertible_unit _ _)

/-- The original two smooth-site maps agree on restrictions after the actual
closed base refinement and chosen normal component, using the same root and pair. -/
theorem restriction_baseComponent_same_root
    {K : Type u} [Field K] (P : PresheafWithTransfers.{v} K) (hP : IsA1Invariant P)
    {A Anew T : SmoothSite (Spec (.of K))}
    [_hAffBase : IsAffine Anew.left] [_hIntegralBase : IsIntegral Anew.left]
    (v : Anew ⟶ A) [_hBaseOpen : IsOpenImmersion v.left]
    [_hBaseClosed : IsClosedImmersion v.left]
    {X Y B : Scheme.{u}} (q : X ⟶ A.left) [_hProper : IsProper q]
    [_hCurveNormal : IsNormal (Limits.pullback q v.left)]
    [_hCurveNoetherian : IsNoetherian (Limits.pullback q v.left)]
    (j : Y ⟶ X) [_hRetainedAffine : IsAffine Y] [IsOpenImmersion j]
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
    [_hBoundarySurjective : Surjective (Limits.pullback.fst (normalComponentOpen x).ι
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
  obtain ⟨hσClosed, hσCartier, hσ₂Cartier, hσq⟩ :=
    baseComponent_action_section_geometry q v.left σ hσ x σ₂ hσ₂
  obtain ⟨hτClosed, hτCartier, hτ₂Cartier, hτq⟩ :=
    baseComponent_action_section_geometry q v.left τ hτ x τ₂ hτ₂
  let := hσClosed
  let := hτClosed
  let := hσCartier
  let := hτCartier
  let := hσ₂Cartier
  let := hτ₂Cartier
  obtain ⟨σRet, hσRet, hfFinal⟩ := exists_baseComponentRetained_section_originalTarget
    v q j κ r hr σ hσ σY hσY σ₂ hσ₂ f hf
  obtain ⟨τRet, hτRet, hgFinal⟩ := exists_baseComponentRetained_section_originalTarget
    v q j κ r hr τ hτ τY hτY τ₂ hτ₂ g hg
  obtain ⟨hAff, hInt, hNoeth, hDom, hComp, hBoundary, hSmooth, hcover⟩ :=
    baseComponent_retained_action_geometry q v.left j d hd x σRet
      (Classical.choice (inferInstance : Nonempty Anew.left))
  let := hAff
  let := hInt
  let := hNoeth
  let := hDom
  let := hComp
  let := hBoundary
  let := hSmooth
  have hTransport := originalRootBaseComponentTransportResult
    F κ v.left b₁ b₂ d i₁ i₂ w₁ w₂ σ τ σ₁ τ₁ σ₂ τ₂
    hs₁ ht₁ hσ₂ hτ₂ aD aE M (k + 1) α e he N eN a bN ha hb
  let rFinal := baseComponentRetainedTargetMap v q j κ r hr
  have hrFinal : rFinal ≫ Limits.pullback.fst Anew.hom T.hom = j₂ ≫ q₂ :=
    baseComponentRetainedTargetMap_fst v q j κ r hr
  exact restriction_of_baseComponentTransportResult P hP Anew T
    F κ v.left b₁ b₂ d i₁ i₂ w₁ w₂ σ τ σ₁ τ₁ σ₂ τ₂ hs₁ ht₁ hσ₂ hτ₂
    aD aE M N k hn α e eN a bN hTransport
    q₂ j₂ hcover rFinal hrFinal hσq hτq σRet τRet hσRet hτRet
    (v ≫ f) (v ≫ g) hfFinal hgFinal

end AlgebraicGeometry.PresheafWithTransfers
