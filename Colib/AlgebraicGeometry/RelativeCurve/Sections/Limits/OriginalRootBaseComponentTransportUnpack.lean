/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.OriginalRootBaseComponentTransportResult

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
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose Scheme.Modules
namespace Stacks.AlgebraicGeometry.ModuleLimits

local instance unpackComponentPullbackInvertible
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    [hM : AlgebraicGeometry.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property M] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property ((pullback f).obj M) :=
  Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry f.toLRSHom.toShHom M hM

local instance unpackComponentUnitInvertible (X : Scheme.{u}) :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (ringSheafCond X)
      (SheafOfModules.unit X.ringCatSheaf) :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (Stacks.SheafOfModules.isInvertible_unit _ _)

/-- Name the literal transported isomorphisms and sections before specializing
n to a successor. All five recovery equalities are retained; this selects no
new root or auxiliary pair. The native action can consume the named witnesses
without reducing recursive tensor-power congruences during unification. -/
theorem originalRootBaseComponentTransportResult_unpack
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
    (N : X₀.Modules)
    (eN : (pullback i₀).obj N ≅ SheafOfModules.unit B₀.ringCatSheaf)
    (a : Γ(((Stacks.SheafOfModules.Tensor.sheafTensor X₀.sheaf).obj M).obj N, ⊤))
    (bN : Γ(N, ⊤))
    (H : OriginalRootBaseComponentTransportResult F κ g b₁ b₂ i₀ i₁ i₂ w₁ w₂
      s₀ t₀ s₁ t₁ s₂ t₂ hs₁ ht₁ hs₂ ht₂ aD₀ aE₀ M n α e N eN a bN) :
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
    let N₁ := (pullback F).obj N
    let NFinal := (pullback κ).obj N₁
    let eN₁ := pullbackBoundaryTrivialization b₁ i₀ i₁ F w₁ N eN
    let eNFinal := pullbackBoundaryTrivialization b₂ i₁ i₂ κ w₂ N₁ eN₁
    let a₁ := Hom.app (pullbackTensorIso F M N).hom ⊤ (pullbackGlobalSections F _ a)
    let bN₁ := pullbackGlobalSections F N bN
    let aFinal := Hom.app (pullbackTensorIso κ M₁ N₁).hom ⊤ (pullbackGlobalSections κ _ a₁)
    let bFinal := pullbackGlobalSections κ N₁ bN₁
    ∃ (αOut : tensorPower X₂.toRingedSpace.presheaf
          (structureSheafRing X₂.toRingedSpace).property MFinal (n : ℤ) ≅
          differenceSheaf s₂.ker t₂.ker)
      (eOut : (pullback i₂).obj MFinal ≅ SheafOfModules.unit B₂.ringCatSheaf)
      (eNOut : (pullback i₂).obj NFinal ≅ SheafOfModules.unit B₂.ringCatSheaf)
      (aOut : Γ(((Stacks.SheafOfModules.Tensor.sheafTensor X₂.sheaf).obj MFinal).obj
        NFinal, ⊤)) (bOut : Γ(NFinal, ⊤)),
      αOut = αFinal ∧ eOut = eFinal ∧ eNOut = eNFinal ∧
      aOut = aFinal ∧ bOut = bFinal ∧
      tensorPowerCongr B₂.presheaf (ringSheafCond B₂) _ _ eOut n =
        boundaryRootPowerIso i₂ MFinal (differenceSheaf s₂.ker t₂.ker) n αOut
          (differenceSheafBoundaryIso i₂ s₂.ker t₂.ker
            (avoids_sectionKernel_openRestriction b₂ i₁ i₂ κ w₂ s₁ s₂ hs₂ aD₁)
            (avoids_sectionKernel_openRestriction b₂ i₁ i₂ κ w₂ t₁ t₂ ht₂ aE₁)) ∧
      Hom.app (pullbackTensorFrame i₂ MFinal NFinal eOut eNOut).hom ⊤
        (pullbackGlobalSections i₂ _ aOut) = (1 : Γ(B₂, ⊤)) ∧
      Hom.app eNOut.hom ⊤ (pullbackGlobalSections i₂ NFinal bOut) = (1 : Γ(B₂, ⊤)) := by
  dsimp only
  obtain ⟨hRoot, ha, hb⟩ := H
  exact ⟨_, _, _, _, _, rfl, rfl, rfl, rfl, rfl, hRoot, ha, hb⟩

end Stacks.AlgebraicGeometry.ModuleLimits
