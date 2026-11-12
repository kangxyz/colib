/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.Divisors.Meromorphic.CanonicalBoundaryFramePullbackTwoStep
public import Colib.AlgebraicGeometry.Divisors.SectionKernelOpenRestriction
public import Colib.AlgebraicGeometry.Modules.Limits.BoundaryRootTransport

/-! # Original root frames through four actual refinements

Nested targets and the original root are retained throughout.
-/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.ModuleLimits Stacks.SheafOfModules.Invertible
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose Scheme.Modules
namespace Stacks.Divisors

/-- Four actual refinements, preserving the nested target used by original-root descent.
No equality of a chosen Cartier comparison with a composite comparison is assumed. -/
theorem differenceSheafBoundaryIso_pullback_four_squares
    {B₀ B₁ B₂ B₃ B₄ X₀ X₁ X₂ X₃ X₄ : Scheme.{u}}
    (b1 : B₁ ⟶ B₀) (f1 : X₁ ⟶ X₀)
    (b2 : B₂ ⟶ B₁) (f2 : X₂ ⟶ X₁)
    (b3 : B₃ ⟶ B₂) (f3 : X₃ ⟶ X₂)
    (b4 : B₄ ⟶ B₃) (f4 : X₄ ⟶ X₃)
    (i0 : B₀ ⟶ X₀)
    (i1 : B₁ ⟶ X₁)
    (i2 : B₂ ⟶ X₂)
    (i3 : B₃ ⟶ X₃)
    (i4 : B₄ ⟶ X₄)
    (w1 : b1 ≫ i0 = i1 ≫ f1)
    (w2 : b2 ≫ i1 = i2 ≫ f2)
    (w3 : b3 ≫ i2 = i3 ≫ f3)
    (w4 : b4 ≫ i3 = i4 ≫ f4)
    (D E : X₀.IdealSheafData)
    [IsEffectiveCartierDivisor D] [IsEffectiveCartierDivisor E]
    [IsPullbackDefined f1 D] [IsPullbackDefined f1 E]
    [IsPullbackDefined f2 (D.comap f1)] [IsPullbackDefined f2 (E.comap f1)]
    [IsPullbackDefined f3 ((D.comap f1).comap f2)] [IsPullbackDefined f3 ((E.comap f1).comap f2)]
    [IsPullbackDefined f4 (((D.comap f1).comap f2).comap f3)] [IsPullbackDefined f4 (((E.comap
      f1).comap f2).comap f3)]
    (aD : ∀ y : B₀, i0 y ∉ D.support) (aE : ∀ y : B₀, i0 y ∉ E.support) :
    let aD1 := avoids_support_comap_square b1 i0 i1 f1 w1 D aD
    let aE1 := avoids_support_comap_square b1 i0 i1 f1 w1 E aE
    let ρ1 := differenceSheafPullbackIso f1 D E
    let Q1 := (Scheme.Modules.pullback f1).obj (differenceSheaf D E)
    let τ1 := pullbackBoundaryTrivialization b1 i0 i1 f1 w1 (differenceSheaf D E)
      (differenceSheafBoundaryIso i0 D E aD aE)
    let δ1 := ρ1
    let aD2 := avoids_support_comap_square b2 i1 i2 f2 w2 (D.comap f1) aD1
    let aE2 := avoids_support_comap_square b2 i1 i2 f2 w2 (E.comap f1) aE1
    let ρ2 := differenceSheafPullbackIso f2 (D.comap f1) (E.comap f1)
    let Q2 := (Scheme.Modules.pullback f2).obj Q1
    let τ2 := pullbackBoundaryTrivialization b2 i1 i2 f2 w2 Q1 τ1
    let δ2 := (Scheme.Modules.pullback f2).mapIso δ1 ≪≫ ρ2
    let aD3 := avoids_support_comap_square b3 i2 i3 f3 w3 ((D.comap f1).comap f2) aD2
    let aE3 := avoids_support_comap_square b3 i2 i3 f3 w3 ((E.comap f1).comap f2) aE2
    let ρ3 := differenceSheafPullbackIso f3 ((D.comap f1).comap f2) ((E.comap f1).comap f2)
    let Q3 := (Scheme.Modules.pullback f3).obj Q2
    let τ3 := pullbackBoundaryTrivialization b3 i2 i3 f3 w3 Q2 τ2
    let δ3 := (Scheme.Modules.pullback f3).mapIso δ2 ≪≫ ρ3
    let aD4 := avoids_support_comap_square b4 i3 i4 f4 w4 (((D.comap f1).comap f2).comap f3) aD3
    let aE4 := avoids_support_comap_square b4 i3 i4 f4 w4 (((E.comap f1).comap f2).comap f3) aE3
    let ρ4 := differenceSheafPullbackIso f4 (((D.comap f1).comap f2).comap f3) (((E.comap
      f1).comap f2).comap f3)
    let _Q4 := (Scheme.Modules.pullback f4).obj Q3
    let τ4 := pullbackBoundaryTrivialization b4 i3 i4 f4 w4 Q3 τ3
    let δ4 := (Scheme.Modules.pullback f4).mapIso δ3 ≪≫ ρ4
    (Scheme.Modules.pullback i4).mapIso δ4 ≪≫
      differenceSheafBoundaryIso i4 ((((D.comap f1).comap f2).comap f3).comap f4) ((((E.comap
        f1).comap f2).comap f3).comap f4) aD4 aE4 = τ4 := by
  intro aD1 aE1 ρ1 Q1 τ1 δ1 aD2 aE2 ρ2 Q2 τ2 δ2 aD3 aE3 ρ3 Q3 τ3 δ3 aD4 aE4 ρ4 _Q4 τ4 δ4
  have h1 : (Scheme.Modules.pullback i1).mapIso δ1 ≪≫
      differenceSheafBoundaryIso i1 (D.comap f1) (E.comap f1) aD1 aE1 = τ1 :=
    differenceSheafBoundaryIso_pullback_square b1 i0 i1 f1 w1 D E aD aE
  have h2 : (Scheme.Modules.pullback i2).mapIso δ2 ≪≫
      differenceSheafBoundaryIso i2 ((D.comap f1).comap f2) ((E.comap f1).comap f2) aD2 aE2 = τ2
        := by
    change (Scheme.Modules.pullback i2).mapIso ((Scheme.Modules.pullback f2).mapIso δ1 ≪≫ ρ2) ≪≫
      _ = _
    rw [Functor.mapIso_trans, Iso.trans_assoc]
    rw [differenceSheafBoundaryIso_pullback_square b2 i1 i2 f2 w2 (D.comap f1) (E.comap f1) aD1 aE1]
    rw [pullbackBoundaryTrivialization_naturality b2 i1 i2 f2 w2 δ1]
    exact congrArg (pullbackBoundaryTrivialization b2 i1 i2 f2 w2 Q1) h1
  have h3 : (Scheme.Modules.pullback i3).mapIso δ3 ≪≫
      differenceSheafBoundaryIso i3 (((D.comap f1).comap f2).comap f3) (((E.comap f1).comap
        f2).comap f3) aD3 aE3 = τ3 := by
    change (Scheme.Modules.pullback i3).mapIso ((Scheme.Modules.pullback f3).mapIso δ2 ≪≫ ρ3) ≪≫
      _ = _
    rw [Functor.mapIso_trans, Iso.trans_assoc]
    rw [differenceSheafBoundaryIso_pullback_square b3 i2 i3 f3 w3 ((D.comap f1).comap f2)
      ((E.comap f1).comap f2) aD2 aE2]
    rw [pullbackBoundaryTrivialization_naturality b3 i2 i3 f3 w3 δ2]
    exact congrArg (pullbackBoundaryTrivialization b3 i2 i3 f3 w3 Q2) h2
  change (Scheme.Modules.pullback i4).mapIso ((Scheme.Modules.pullback f4).mapIso δ3 ≪≫ ρ4) ≪≫ _ = _
  rw [Functor.mapIso_trans, Iso.trans_assoc]
  rw [differenceSheafBoundaryIso_pullback_square b4 i3 i4 f4 w4 (((D.comap f1).comap f2).comap
    f3) (((E.comap f1).comap f2).comap f3) aD3 aE3]
  rw [pullbackBoundaryTrivialization_naturality b4 i3 i4 f4 w4 δ3]
  exact congrArg (pullbackBoundaryTrivialization b4 i3 i4 f4 w4 Q3) h3

end Stacks.Divisors

namespace Stacks.AlgebraicGeometry.ModuleLimits

/-- Change only the target of the SAME root, retaining its full-boundary frame.
This specializes the existing ambient-and-target transport to the identity ambient iso. -/
theorem original_root_frame_change_target
    {B X : Scheme.{u}} (i : B ⟶ X) (M Q R : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property M]
    (n : ℕ)
    (α : tensorPower X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property M (n : ℤ) ≅ Q)
    (δ : Q ≅ R)
    (τ : (Scheme.Modules.pullback i).obj R ≅ SheafOfModules.unit B.ringCatSheaf)
    (e : (Scheme.Modules.pullback i).obj M ≅ SheafOfModules.unit B.ringCatSheaf)
    (he : tensorPowerCongr B.toRingedSpace.presheaf
      (structureSheafRing B.toRingedSpace).property _ _ e n =
      boundaryRootPowerIso i M Q n α ((Scheme.Modules.pullback i).mapIso δ ≪≫ τ)) :
    tensorPowerCongr B.toRingedSpace.presheaf
      (structureSheafRing B.toRingedSpace).property _ _ e n =
      boundaryRootPowerIso i M R n (α ≪≫ δ) τ := by
  have hr := tensorPowerCongr_refl X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property (L := M) n
  have hroot := (congrArg (fun z => z ≪≫ (α ≪≫ δ)) hr).trans (Iso.refl_trans _)
  have h := boundaryRootPowerIso_transport i M M Q R (Iso.refl M) n
    α (α ≪≫ δ) δ τ hroot.symm
  have hb := tensorPowerCongr_refl B.toRingedSpace.presheaf
    (structureSheafRing B.toRingedSpace).property (L := (Scheme.Modules.pullback i).obj M) n
  have hm := congrArg (fun z => tensorPowerCongr B.toRingedSpace.presheaf
    (structureSheafRing B.toRingedSpace).property _ _ z n)
      ((Scheme.Modules.pullback i).mapIso_refl M)
  exact he.trans (h.trans ((congrArg
    (fun z => z ≪≫ boundaryRootPowerIso i M R n (α ≪≫ δ) τ) (hm.trans hb)).trans
      (Iso.refl_trans _)))

/-- The canonical full-boundary frame of actual section kernels is insensitive to
replacing iterated comap ideals by the equal actual kernels. The original root and
its frame are unchanged. This is the terminal step AFTER the four-square theorem:
use its equality to rewrite the descended frame before applying this lemma. -/
theorem original_root_frame_to_actual_kernels
    {B X S : Scheme.{u}} (i : B ⟶ X) (M : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property M]
    (D E : X.IdealSheafData) (σ τ : S ⟶ X)
    [Stacks.Divisors.IsEffectiveCartierDivisor D]
    [Stacks.Divisors.IsEffectiveCartierDivisor E]
    [Stacks.Divisors.IsEffectiveCartierDivisor σ.ker]
    [Stacks.Divisors.IsEffectiveCartierDivisor τ.ker]
    (hD : D = σ.ker) (hE : E = τ.ker)
    (aD : ∀ y : B, i y ∉ D.support) (aE : ∀ y : B, i y ∉ E.support)
    (aσ : ∀ y : B, i y ∉ σ.ker.support) (aτ : ∀ y : B, i y ∉ τ.ker.support)
    (n : ℕ)
    (α : tensorPower X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property M (n : ℤ) ≅
      Stacks.Divisors.differenceSheaf D E)
    (e : (Scheme.Modules.pullback i).obj M ≅ SheafOfModules.unit B.ringCatSheaf)
    (he : tensorPowerCongr B.toRingedSpace.presheaf
      (structureSheafRing B.toRingedSpace).property _ _ e n =
      boundaryRootPowerIso i M _ n α
        (Stacks.Divisors.differenceSheafBoundaryIso i D E aD aE)) :
    tensorPowerCongr B.toRingedSpace.presheaf
      (structureSheafRing B.toRingedSpace).property _ _ e n =
      boundaryRootPowerIso i M _ n
        (α ≪≫ eqToIso (congrArg₂ Stacks.Divisors.differenceSheaf hD hE))
        (Stacks.Divisors.differenceSheafBoundaryIso i σ.ker τ.ker aσ aτ) := by
  apply original_root_frame_change_target i M _ _ n α
    (eqToIso (congrArg₂ Stacks.Divisors.differenceSheaf hD hE))
    (Stacks.Divisors.differenceSheafBoundaryIso i σ.ker τ.ker aσ aτ) e
  rw [Stacks.Divisors.differenceSheafBoundaryIso_congr i D E σ.ker τ.ker
    hD hE aD aE aσ aτ]
  exact he

end Stacks.AlgebraicGeometry.ModuleLimits
