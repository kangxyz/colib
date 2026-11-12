/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.Invertible.BoundaryRootPullback
public import Colib.AlgebraicGeometry.Divisors.Meromorphic.OriginalRootFourStageCanonicalFrame
public import Colib.AlgebraicGeometry.Modules.Invertible.PullbackTensorFrameComparison
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.BoundaryScalarPullback
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.OriginalRootFinalNumerator

/-! # Restrict the same original root and auxiliary pair to the actual component

Only literal pullbacks of M, N, their frames and sections are used. The ambient
open inclusion need not give a Cartesian whole-curve square over the base.
Canonical target compatibility is proved from the actual section factors.
The two theorems together give the canonical root equation and the two literal
boundary-one equations for exactly the same restricted objects.
-/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
open Stacks.SheafOfModules.Invertible Stacks.Divisors
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose Scheme.Modules
namespace Stacks.AlgebraicGeometry.ModuleLimits

local instance openRestrictionRootPullbackInvertible
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    [hM : AlgebraicGeometry.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property M] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property ((pullback f).obj M) :=
  Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry f.toLRSHom.toShHom M hM

/-- Literal restriction of the specified root targets the actual factored-section
kernels and their canonical full-boundary frame. No new root is chosen. -/
theorem original_root_frame_openRestriction {S B' B X' X : Scheme.{u}}
    (b : B' ⟶ B) (i : B ⟶ X) (i' : B' ⟶ X') (f : X' ⟶ X)
    [IsOpenImmersion f] (w : b ≫ i = i' ≫ f)
    (s t : S ⟶ X) [IsClosedImmersion s] [IsClosedImmersion t]
    (s' t' : S ⟶ X') (hs : s' ≫ f = s) (ht : t' ≫ f = t)
    [IsEffectiveCartierDivisor s.ker] [IsEffectiveCartierDivisor t.ker]
    [IsEffectiveCartierDivisor s'.ker] [IsEffectiveCartierDivisor t'.ker]
    (aD : ∀ y : B, i y ∉ s.ker.support) (aE : ∀ y : B, i y ∉ t.ker.support)
    (M : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property M]
    (n : ℕ)
    (α : tensorPower X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property M (n : ℤ) ≅
        differenceSheaf s.ker t.ker)
    (e : (pullback i).obj M ≅ SheafOfModules.unit B.ringCatSheaf)
    (he : tensorPowerCongr B.toRingedSpace.presheaf
      (structureSheafRing B.toRingedSpace).property _ _ e n =
        boundaryRootPowerIso i M _ n α (differenceSheafBoundaryIso i s.ker t.ker aD aE)) :
    tensorPowerCongr B'.toRingedSpace.presheaf
      (structureSheafRing B'.toRingedSpace).property _ _
      (pullbackBoundaryTrivialization b i i' f w M e) n =
    boundaryRootPowerIso i' ((pullback f).obj M) (differenceSheaf s'.ker t'.ker) n
      (((pullbackTensorPowerIso f M n).symm ≪≫ (pullback f).mapIso α) ≪≫
        sectionKernelDifferenceOpenRestrictionIso f s t s' t' hs ht)
      (differenceSheafBoundaryIso i' s'.ker t'.ker
        (avoids_sectionKernel_openRestriction b i i' f w s s' hs aD)
        (avoids_sectionKernel_openRestriction b i i' f w t t' ht aE)) := by
  apply original_root_frame_change_target i' ((pullback f).obj M)
    ((pullback f).obj (differenceSheaf s.ker t.ker)) (differenceSheaf s'.ker t'.ker) n
    ((pullbackTensorPowerIso f M n).symm ≪≫ (pullback f).mapIso α)
    (sectionKernelDifferenceOpenRestrictionIso f s t s' t' hs ht)
    (differenceSheafBoundaryIso i' s'.ker t'.ker
      (avoids_sectionKernel_openRestriction b i i' f w s s' hs aD)
      (avoids_sectionKernel_openRestriction b i i' f w t t' ht aE))
    (pullbackBoundaryTrivialization b i i' f w M e)
  rw [sectionKernelDifferenceOpenRestrictionIso_boundary b i i' f w s t s' t' hs ht aD aE]
  exact boundary_root_frame_pullback b i i' f w M (differenceSheaf s.ker t.ker) n α
    (differenceSheafBoundaryIso i s.ker t.ker aD aE) e he

/-- The literal pulled-back numerator, with the native tensor comparison, and
literal pulled-back denominator retain both full-boundary unit equations.
This uses the very same M, N and e as the root restriction theorem. -/
theorem original_auxiliary_pair_openRestriction_one {B' B X' X : Scheme.{u}}
    (b : B' ⟶ B) (i : B ⟶ X) (i' : B' ⟶ X') (f : X' ⟶ X)
    (w : b ≫ i = i' ≫ f) (M N : X.Modules)
    (e : (pullback i).obj M ≅ SheafOfModules.unit B.ringCatSheaf)
    (eN : (pullback i).obj N ≅ SheafOfModules.unit B.ringCatSheaf)
    (a : Γ(((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj M).obj N, ⊤))
    (bN : Γ(N, ⊤))
    (ha : Hom.app (pullbackTensorFrame i M N e eN).hom ⊤
      (pullbackGlobalSections i _ a) = (1 : Γ(B, ⊤)))
    (hb : Hom.app eN.hom ⊤ (pullbackGlobalSections i N bN) = (1 : Γ(B, ⊤))) :
    Hom.app (pullbackTensorFrame i' ((pullback f).obj M) ((pullback f).obj N)
      (pullbackBoundaryTrivialization b i i' f w M e)
      (pullbackBoundaryTrivialization b i i' f w N eN)).hom ⊤
      (pullbackGlobalSections i' _
        (Hom.app (pullbackTensorIso f M N).hom ⊤ (pullbackGlobalSections f _ a))) =
          (1 : Γ(B', ⊤)) ∧
    Hom.app (pullbackBoundaryTrivialization b i i' f w N eN).hom ⊤
      (pullbackGlobalSections i' _ (pullbackGlobalSections f N bN)) = (1 : Γ(B', ⊤)) := by
  constructor
  · apply original_auxiliary_numerator_final_one i' _ _ (pullbackTensorIso f M N)
      (pullbackTensorFrame i' ((pullback f).obj M) ((pullback f).obj N)
        (pullbackBoundaryTrivialization b i i' f w M e)
        (pullbackBoundaryTrivialization b i i' f w N eN))
      (pullbackGlobalSections f _ a)
    rw [← pullbackBoundaryTrivialization_pullbackTensorFrame b i i' f w M N e eN]
    exact pullbackBoundaryTrivialization_section_one b i i' f w _
      (pullbackTensorFrame i M N e eN) a ha
  · exact pullbackBoundaryTrivialization_section_one b i i' f w N eN bN hb

end Stacks.AlgebraicGeometry.ModuleLimits
