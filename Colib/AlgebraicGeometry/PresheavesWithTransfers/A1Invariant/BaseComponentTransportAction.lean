/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.OriginalRootBaseComponentTransportResult
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1Invariant.BoundaryFramedSectionActionNative

/-! # Consume the same two-step root transport before specializing its geometry

The named transport result is consumed with abstract ambient schemes and actual
section squares. The actual component caller supplies constructed geometry and
maps, not a producer for root compatibility. No root or auxiliary pair is chosen.
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

local instance transportActionAG (X : Scheme.{u}) (M : X.Modules)
    [h : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property M :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ h

local instance transportActionPB {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    [Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatIsSheaf M] :
    Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf
      ((pullback f).obj M) :=
  Stacks.PullbackMonoidalSheaf.isInvertible_pullbackFunctor_obj f.toLRSHom.toShHom M

local instance transportActionUnit (X : Scheme.{u}) :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (ringSheafCond X)
      (SheafOfModules.unit X.ringCatSheaf) :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (Stacks.SheafOfModules.isInvertible_unit _ _)

/-- The original transported root and auxiliary sections give the actual
restriction equality. All nested modules and sections are exactly those of H. -/
theorem restriction_of_baseComponentTransportResult
    {K : Type u} [Field K] (P : PresheafWithTransfers.{v} K) (hP : IsA1Invariant P)
    (A T : SmoothSite (Spec (.of K))) [IsAffine A.left] [IsIntegral A.left]
    {S₀ B₀ B₁ B₂ X₀ X₁ X₂ U : Scheme.{u}}
    [IsIntegral X₂] [IsNoetherian X₂] [Nonempty B₂]
    [IsIntegral U] [IsNoetherian U] [U.IsQuasiAffine]
    (F : X₁ ⟶ X₀) (κ : X₂ ⟶ X₁) [IsOpenImmersion κ] (gBase : A.left ⟶ S₀)
    (b₁ : B₁ ⟶ B₀) (b₂ : B₂ ⟶ B₁)
    (i₀ : B₀ ⟶ X₀) (i₁ : B₁ ⟶ X₁) (i₂ : B₂ ⟶ X₂)
    (w₁ : b₁ ≫ i₀ = i₁ ≫ F) (w₂ : b₂ ≫ i₁ = i₂ ≫ κ)
    (s₀ t₀ : S₀ ⟶ X₀) (s₁ t₁ : A.left ⟶ X₁) (s₂ t₂ : A.left ⟶ X₂)
    [IsClosedImmersion s₀] [IsClosedImmersion t₀]
    [IsClosedImmersion s₁] [IsClosedImmersion t₁]
    (hs₁ : IsPullback s₁ gBase F s₀) (ht₁ : IsPullback t₁ gBase F t₀)
    (hs₂ : s₂ ≫ κ = s₁) (ht₂ : t₂ ≫ κ = t₁)
    [IsEffectiveCartierDivisor s₀.ker] [IsEffectiveCartierDivisor t₀.ker]
    [IsEffectiveCartierDivisor s₁.ker] [IsEffectiveCartierDivisor t₁.ker]
    [IsEffectiveCartierDivisor s₂.ker] [IsEffectiveCartierDivisor t₂.ker]
    (aD₀ : ∀ y : B₀, i₀ y ∉ s₀.ker.support)
    (aE₀ : ∀ y : B₀, i₀ y ∉ t₀.ker.support)
    (M N : X₀.Modules)
    [hM : Stacks.SheafOfModules.IsInvertible X₀.presheaf X₀.ringCatIsSheaf M]
    [Stacks.SheafOfModules.IsInvertible X₀.presheaf X₀.ringCatIsSheaf N]
    (k : ℕ) (hn : ∀ z : sections P ((Cor.graphFunctor K).obj A), (k + 1) • z = 0)
    (α : Stacks.SheafOfModules.schemeTensorPower X₀ M hM ((k + 1 : ℕ) : ℤ) ≅
      differenceSheaf s₀.ker t₀.ker)
    (e : (pullback i₀).obj M ≅ SheafOfModules.unit B₀.ringCatSheaf)
    (eN : (pullback i₀).obj N ≅ SheafOfModules.unit B₀.ringCatSheaf)
    (a : Γ(((Stacks.SheafOfModules.Tensor.sheafTensor X₀.sheaf).obj M).obj N, ⊤))
    (bN : Γ(N, ⊤))
    (H : OriginalRootBaseComponentTransportResult F κ gBase b₁ b₂ i₀ i₁ i₂ w₁ w₂
      s₀ t₀ s₁ t₁ s₂ t₂ hs₁ ht₁ hs₂ ht₂ aD₀ aE₀ M (k + 1) α e N eN a bN)
    (q : X₂ ⟶ A.left) [IsProper q] (j : U ⟶ X₂)
    [IsOpenImmersion j] [IsDominant j] [SmoothOfRelativeDimension 1 (j ≫ q)]
    (hcover : ∀ y : X₂, y ∈ Set.range j ∨ y ∈ Set.range i₂)
    (r : U ⟶ Limits.pullback A.hom T.hom)
    (hr : r ≫ Limits.pullback.fst A.hom T.hom = j ≫ q)
    (hsq : s₂ ≫ q = 𝟙 _) (htq : t₂ ≫ q = 𝟙 _)
    (sU tU : A.left ⟶ U) (hsU : sU ≫ j = s₂) (htU : tU ≫ j = t₂)
    (fFinal gFinal : A ⟶ T)
    (hf : fFinal.left = sU ≫ r ≫ Limits.pullback.snd A.hom T.hom)
    (hg : gFinal.left = tU ≫ r ≫ Limits.pullback.snd A.hom T.hom) :
    ((toPresheaf K).obj P).map fFinal.op = ((toPresheaf K).obj P).map gFinal.op := by
  let aD₁ : ∀ y : B₁, i₁ y ∉ s₁.ker.support :=
    avoids_sectionKernel_cartesianSections b₁ i₀ i₁ F gBase w₁ s₀ s₁ hs₁ aD₀
  let aE₁ : ∀ y : B₁, i₁ y ∉ t₁.ker.support :=
    avoids_sectionKernel_cartesianSections b₁ i₀ i₁ F gBase w₁ t₀ t₁ ht₁ aE₀
  let aD₂ : ∀ y : B₂, i₂ y ∉ s₂.ker.support :=
    avoids_sectionKernel_openRestriction b₂ i₁ i₂ κ w₂ s₁ s₂ hs₂ aD₁
  let aE₂ : ∀ y : B₂, i₂ y ∉ t₂.ker.support :=
    avoids_sectionKernel_openRestriction b₂ i₁ i₂ κ w₂ t₁ t₂ ht₂ aE₁
  let M₁ : X₁.Modules := (pullback F).obj M
  let N₁ : X₁.Modules := (pullback F).obj N
  let M₂ : X₂.Modules := (pullback κ).obj M₁
  let N₂ : X₂.Modules := (pullback κ).obj N₁
  let α₁ := ((pullbackTensorPowerIso F M (k + 1)).symm ≪≫ (pullback F).mapIso α) ≪≫
    sectionKernelDifferenceOfCartesianSectionsIso F gBase s₀ t₀ s₁ t₁ hs₁ ht₁
  let α₂ := ((pullbackTensorPowerIso κ M₁ (k + 1)).symm ≪≫ (pullback κ).mapIso α₁) ≪≫
    sectionKernelDifferenceOpenRestrictionIso κ s₁ t₁ s₂ t₂ hs₂ ht₂
  let e₁ := pullbackBoundaryTrivialization b₁ i₀ i₁ F w₁ M e
  let eN₁ := pullbackBoundaryTrivialization b₁ i₀ i₁ F w₁ N eN
  let e₂ := pullbackBoundaryTrivialization b₂ i₁ i₂ κ w₂ M₁ e₁
  let eN₂ := pullbackBoundaryTrivialization b₂ i₁ i₂ κ w₂ N₁ eN₁
  let a₁ := Hom.app (X := X₁) (pullbackTensorIso F M N).hom ⊤
    (pullbackGlobalSections F _ a)
  let a₂ := Hom.app (X := X₂) (pullbackTensorIso κ M₁ N₁).hom ⊤
    (pullbackGlobalSections κ _ a₁)
  let b₂N := pullbackGlobalSections κ N₁ (pullbackGlobalSections F N bN)
  exact restriction_boundary_framed_section_pair_eq_native P hP A T q i₂ j hcover r hr
    s₂ t₂ hsq htq sU tU hsU htU aD₂ aE₂ M₂ N₂ k hn α₂ e₂ eN₂ a₂ b₂N
    H.2.1 H.2.2 fFinal gFinal hf hg H.1

end AlgebraicGeometry.PresheafWithTransfers
