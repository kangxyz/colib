/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.OriginalRootCartesianSections
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.OriginalRootOpenRestriction

/-! # The same root and auxiliary pair through base restriction and component restriction

The first map has actual source-changing Cartesian section squares. The second
is the actual open component inclusion with same-base section factors. Both
ambient and boundary pullbacks remain nested. No composite-pullback identification,
new root, or whole-curve Cartesian assertion for the component is used.
-/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
open Stacks.SheafOfModules.Invertible Stacks.Divisors
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose Scheme.Modules
namespace Stacks.AlgebraicGeometry.ModuleLimits

local instance baseComponentPullbackInvertible
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    [hM : AlgebraicGeometry.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property M] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property ((pullback f).obj M) :=
  Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry f.toLRSHom.toShHom M hM

/-- The original canonical root after the two actual restrictions. The final root
is exactly κ*(F*M), and its power map uses the two native comparisons in order. -/
theorem original_root_frame_base_component
    {S₀ S₁ B₀ B₁ B₂ X₀ X₁ X₂ : Scheme.{u}}
    (F : X₁ ⟶ X₀) (κ : X₂ ⟶ X₁) [IsOpenImmersion κ] (g : S₁ ⟶ S₀)
    (b₁ : B₁ ⟶ B₀) (b₂ : B₂ ⟶ B₁)
    (i₀ : B₀ ⟶ X₀) (i₁ : B₁ ⟶ X₁) (i₂ : B₂ ⟶ X₂)
    (w₁ : b₁ ≫ i₀ = i₁ ≫ F) (w₂ : b₂ ≫ i₁ = i₂ ≫ κ)
    (s₀ t₀ : S₀ ⟶ X₀) (s₁ t₁ : S₁ ⟶ X₁) (s₂ t₂ : S₁ ⟶ X₂)
    [IsClosedImmersion s₀] [IsClosedImmersion t₀]
    [IsClosedImmersion s₁] [IsClosedImmersion t₁]
    (hs₁ : IsPullback s₁ g F s₀) (ht₁ : IsPullback t₁ g F t₀)
    (hs₂ : s₂ ≫ κ = s₁) (ht₂ : t₂ ≫ κ = t₁)
    [IsEffectiveCartierDivisor s₀.ker] [IsEffectiveCartierDivisor t₀.ker]
    [IsEffectiveCartierDivisor s₁.ker] [IsEffectiveCartierDivisor t₁.ker]
    [IsEffectiveCartierDivisor s₂.ker] [IsEffectiveCartierDivisor t₂.ker]
    (aD₀ : ∀ y : B₀, i₀ y ∉ s₀.ker.support)
    (aE₀ : ∀ y : B₀, i₀ y ∉ t₀.ker.support)
    (M : X₀.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X₀.toRingedSpace.presheaf
      (structureSheafRing X₀.toRingedSpace).property M]
    (n : ℕ)
    (α : tensorPower X₀.toRingedSpace.presheaf
      (structureSheafRing X₀.toRingedSpace).property M (n : ℤ) ≅ differenceSheaf s₀.ker t₀.ker)
    (e : (pullback i₀).obj M ≅ SheafOfModules.unit B₀.ringCatSheaf)
    (he : tensorPowerCongr B₀.toRingedSpace.presheaf
      (structureSheafRing B₀.toRingedSpace).property _ _ e n =
      boundaryRootPowerIso i₀ M _ n α (differenceSheafBoundaryIso i₀ s₀.ker t₀.ker aD₀ aE₀)) :
    let M₁ := (pullback F).obj M
    let MFinal := (pullback κ).obj M₁
    let aD₁ := avoids_sectionKernel_cartesianSections b₁ i₀ i₁ F g w₁ s₀ s₁ hs₁ aD₀
    let aE₁ := avoids_sectionKernel_cartesianSections b₁ i₀ i₁ F g w₁ t₀ t₁ ht₁ aE₀
    let α₁ := ((pullbackTensorPowerIso F M n).symm ≪≫ (pullback F).mapIso α) ≪≫
      sectionKernelDifferenceOfCartesianSectionsIso F g s₀ t₀ s₁ t₁ hs₁ ht₁
    let e₁ := pullbackBoundaryTrivialization b₁ i₀ i₁ F w₁ M e
    let αFinal := ((pullbackTensorPowerIso κ M₁ n).symm ≪≫ (pullback κ).mapIso α₁) ≪≫
      sectionKernelDifferenceOpenRestrictionIso κ s₁ t₁ s₂ t₂ hs₂ ht₂
    let eFinal := pullbackBoundaryTrivialization b₂ i₁ i₂ κ w₂ M₁ e₁
    tensorPowerCongr B₂.toRingedSpace.presheaf
      (structureSheafRing B₂.toRingedSpace).property _ _ eFinal n =
      boundaryRootPowerIso i₂ MFinal (differenceSheaf s₂.ker t₂.ker) n αFinal
        (differenceSheafBoundaryIso i₂ s₂.ker t₂.ker
          (avoids_sectionKernel_openRestriction b₂ i₁ i₂ κ w₂ s₁ s₂ hs₂ aD₁)
          (avoids_sectionKernel_openRestriction b₂ i₁ i₂ κ w₂ t₁ t₂ ht₂ aE₁)) := by
  have h₁ := original_root_frame_cartesianSections b₁ i₀ i₁ F g w₁
    s₀ t₀ s₁ t₁ hs₁ ht₁ aD₀ aE₀ M n α e he
  exact original_root_frame_openRestriction b₂ i₁ i₂ κ w₂
    s₁ t₁ s₂ t₂ hs₂ ht₂
    (avoids_sectionKernel_cartesianSections b₁ i₀ i₁ F g w₁ s₀ s₁ hs₁ aD₀)
    (avoids_sectionKernel_cartesianSections b₁ i₀ i₁ F g w₁ t₀ t₁ ht₁ aE₀)
    ((pullback F).obj M) n
    (((pullbackTensorPowerIso F M n).symm ≪≫ (pullback F).mapIso α) ≪≫
      sectionKernelDifferenceOfCartesianSectionsIso F g s₀ t₀ s₁ t₁ hs₁ ht₁)
    (pullbackBoundaryTrivialization b₁ i₀ i₁ F w₁ M e) h₁

/-- The same auxiliary pair after both actual restrictions, including both native
tensor comparisons on its numerator. The frames agree literally with the root
transport above; there is no independent choice of a final root or frame. -/
theorem original_auxiliary_pair_base_component_one
    {B₀ B₁ B₂ X₀ X₁ X₂ : Scheme.{u}}
    (F : X₁ ⟶ X₀) (κ : X₂ ⟶ X₁)
    (b₁ : B₁ ⟶ B₀) (b₂ : B₂ ⟶ B₁)
    (i₀ : B₀ ⟶ X₀) (i₁ : B₁ ⟶ X₁) (i₂ : B₂ ⟶ X₂)
    (w₁ : b₁ ≫ i₀ = i₁ ≫ F) (w₂ : b₂ ≫ i₁ = i₂ ≫ κ)
    (M N : X₀.Modules)
    (e : (pullback i₀).obj M ≅ SheafOfModules.unit B₀.ringCatSheaf)
    (eN : (pullback i₀).obj N ≅ SheafOfModules.unit B₀.ringCatSheaf)
    (a : Γ(((Stacks.SheafOfModules.Tensor.sheafTensor X₀.sheaf).obj M).obj N, ⊤))
    (bN : Γ(N, ⊤))
    (ha : Hom.app (pullbackTensorFrame i₀ M N e eN).hom ⊤
      (pullbackGlobalSections i₀ _ a) = (1 : Γ(B₀, ⊤)))
    (hb : Hom.app eN.hom ⊤ (pullbackGlobalSections i₀ N bN) = (1 : Γ(B₀, ⊤))) :
    let M₁ := (pullback F).obj M
    let N₁ := (pullback F).obj N
    let MFinal := (pullback κ).obj M₁
    let NFinal := (pullback κ).obj N₁
    let e₁ := pullbackBoundaryTrivialization b₁ i₀ i₁ F w₁ M e
    let eN₁ := pullbackBoundaryTrivialization b₁ i₀ i₁ F w₁ N eN
    let eFinal := pullbackBoundaryTrivialization b₂ i₁ i₂ κ w₂ M₁ e₁
    let eNFinal := pullbackBoundaryTrivialization b₂ i₁ i₂ κ w₂ N₁ eN₁
    let a₁ := Hom.app (pullbackTensorIso F M N).hom ⊤ (pullbackGlobalSections F _ a)
    let bN₁ := pullbackGlobalSections F N bN
    let aFinal := Hom.app (pullbackTensorIso κ M₁ N₁).hom ⊤ (pullbackGlobalSections κ _ a₁)
    let bFinal := pullbackGlobalSections κ N₁ bN₁
    Hom.app (pullbackTensorFrame i₂ MFinal NFinal eFinal eNFinal).hom ⊤
      (pullbackGlobalSections i₂ _ aFinal) = (1 : Γ(B₂, ⊤)) ∧
    Hom.app eNFinal.hom ⊤ (pullbackGlobalSections i₂ NFinal bFinal) = (1 : Γ(B₂, ⊤)) := by
  have h₁ := original_auxiliary_pair_openRestriction_one
    b₁ i₀ i₁ F w₁ M N e eN a bN ha hb
  exact original_auxiliary_pair_openRestriction_one b₂ i₁ i₂ κ w₂
    ((pullback F).obj M) ((pullback F).obj N)
    (pullbackBoundaryTrivialization b₁ i₀ i₁ F w₁ M e)
    (pullbackBoundaryTrivialization b₁ i₀ i₁ F w₁ N eN)
    (Hom.app (pullbackTensorIso F M N).hom ⊤ (pullbackGlobalSections F _ a))
    (pullbackGlobalSections F N bN) h₁.1 h₁.2

end Stacks.AlgebraicGeometry.ModuleLimits
