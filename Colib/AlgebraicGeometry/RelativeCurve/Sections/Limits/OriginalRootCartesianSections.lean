/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.Invertible.BoundaryRootPullback
public import Colib.AlgebraicGeometry.Divisors.Meromorphic.OriginalRootFourStageCanonicalFrame

/-! # The same canonical root under actual Cartesian section squares

The section sources may change. Only the two real section pullback squares are
required, not a Cartesian square for the entire ambient family. Full kernels,
canonical boundary frames, and the original root are transported literally.
-/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
open Stacks.SheafOfModules.Invertible Stacks.Divisors
open Stacks.AlgebraicGeometry.ModuleLimits
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose Scheme.Modules
namespace Stacks.Divisors

/-- Actual Cartier kernels make pullback of the original kernel defined. -/
theorem isPullbackDefined_cartesianSection
    {S' S X' X : Scheme.{u}} (f : X' ⟶ X) (g : S' ⟶ S)
    (s : S ⟶ X) [IsClosedImmersion s] (s' : S' ⟶ X')
    (hs : IsPullback s' g f s) [IsEffectiveCartierDivisor s'.ker] :
    IsPullbackDefined f s.ker := by
  change IsEffectiveCartierDivisor (s.ker.comap f)
  rw [← Scheme.ker_eq_comap_of_isPullback s' g f s hs]
  infer_instance

/-- The actual signed kernel comparison for the supplied section squares. -/
def sectionKernelDifferenceOfCartesianSectionsIso
    {S' S X' X : Scheme.{u}} (f : X' ⟶ X) (g : S' ⟶ S)
    (s t : S ⟶ X) [IsClosedImmersion s] [IsClosedImmersion t]
    (s' t' : S' ⟶ X') (hs : IsPullback s' g f s) (ht : IsPullback t' g f t)
    [IsEffectiveCartierDivisor s.ker] [IsEffectiveCartierDivisor t.ker]
    [IsEffectiveCartierDivisor s'.ker] [IsEffectiveCartierDivisor t'.ker] :
    (pullback f).obj (differenceSheaf s.ker t.ker) ≅ differenceSheaf s'.ker t'.ker := by
  let := isPullbackDefined_cartesianSection f g s s' hs
  let := isPullbackDefined_cartesianSection f g t t' ht
  exact differenceSheafPullbackIso f s.ker t.ker ≪≫
    eqToIso (congrArg₂ differenceSheaf
      (Scheme.ker_eq_comap_of_isPullback s' g f s hs).symm
      (Scheme.ker_eq_comap_of_isPullback t' g f t ht).symm)

/-- The original full-boundary avoidance survives on actual Cartesian section kernels. -/
theorem avoids_sectionKernel_cartesianSections {S' S B' B X' X : Scheme.{u}}
    (b : B' ⟶ B) (i : B ⟶ X) (i' : B' ⟶ X') (f : X' ⟶ X) (g : S' ⟶ S)
    (w : b ≫ i = i' ≫ f)
    (s : S ⟶ X) [IsClosedImmersion s] (s' : S' ⟶ X') (hs : IsPullback s' g f s)
    (a : ∀ y : B, i y ∉ s.ker.support) : ∀ y : B', i' y ∉ s'.ker.support := by
  rw [Scheme.ker_eq_comap_of_isPullback s' g f s hs]
  exact avoids_support_comap_square b i i' f w s.ker a

/-- The specified kernel comparison preserves the canonical full-boundary frame. -/
theorem sectionKernelDifferenceOfCartesianSectionsIso_boundary
    {S' S B' B X' X : Scheme.{u}}
    (b : B' ⟶ B) (i : B ⟶ X) (i' : B' ⟶ X') (f : X' ⟶ X) (g : S' ⟶ S)
    (w : b ≫ i = i' ≫ f)
    (s t : S ⟶ X) [IsClosedImmersion s] [IsClosedImmersion t]
    (s' t' : S' ⟶ X') (hs : IsPullback s' g f s) (ht : IsPullback t' g f t)
    [IsEffectiveCartierDivisor s.ker] [IsEffectiveCartierDivisor t.ker]
    [IsEffectiveCartierDivisor s'.ker] [IsEffectiveCartierDivisor t'.ker]
    (aD : ∀ y : B, i y ∉ s.ker.support) (aE : ∀ y : B, i y ∉ t.ker.support) :
    (pullback i').mapIso (sectionKernelDifferenceOfCartesianSectionsIso f g s t s' t' hs ht) ≪≫
      differenceSheafBoundaryIso i' s'.ker t'.ker
        (avoids_sectionKernel_cartesianSections b i i' f g w s s' hs aD)
        (avoids_sectionKernel_cartesianSections b i i' f g w t t' ht aE) =
    pullbackBoundaryTrivialization b i i' f w (differenceSheaf s.ker t.ker)
      (differenceSheafBoundaryIso i s.ker t.ker aD aE) := by
  let := isPullbackDefined_cartesianSection f g s s' hs
  let := isPullbackDefined_cartesianSection f g t t' ht
  rw [sectionKernelDifferenceOfCartesianSectionsIso, Functor.mapIso_trans, Iso.trans_assoc]
  rw [differenceSheafBoundaryIso_congr i' (s.ker.comap f) (t.ker.comap f) s'.ker t'.ker
    (Scheme.ker_eq_comap_of_isPullback s' g f s hs).symm
    (Scheme.ker_eq_comap_of_isPullback t' g f t ht).symm
    (avoids_support_comap_square b i i' f w s.ker aD)
    (avoids_support_comap_square b i i' f w t.ker aE)]
  exact differenceSheafBoundaryIso_pullback_square b i i' f w s.ker t.ker aD aE

end Stacks.Divisors

namespace Stacks.AlgebraicGeometry.ModuleLimits

local instance cartesianSectionsRootPullbackInvertible
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    [hM : AlgebraicGeometry.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property M] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property ((pullback f).obj M) :=
  Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry f.toLRSHom.toShHom M hM

/-- Literal pullback of the specified root targets the actual Cartesian-section
kernels and their canonical full-boundary frame. No new root is chosen. -/
theorem original_root_frame_cartesianSections {S' S B' B X' X : Scheme.{u}}
    (b : B' ⟶ B) (i : B ⟶ X) (i' : B' ⟶ X') (f : X' ⟶ X) (g : S' ⟶ S)
    (w : b ≫ i = i' ≫ f)
    (s t : S ⟶ X) [IsClosedImmersion s] [IsClosedImmersion t]
    (s' t' : S' ⟶ X') (hs : IsPullback s' g f s) (ht : IsPullback t' g f t)
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
        sectionKernelDifferenceOfCartesianSectionsIso f g s t s' t' hs ht)
      (differenceSheafBoundaryIso i' s'.ker t'.ker
        (avoids_sectionKernel_cartesianSections b i i' f g w s s' hs aD)
        (avoids_sectionKernel_cartesianSections b i i' f g w t t' ht aE)) := by
  apply original_root_frame_change_target i' ((pullback f).obj M)
    ((pullback f).obj (differenceSheaf s.ker t.ker)) (differenceSheaf s'.ker t'.ker) n
    ((pullbackTensorPowerIso f M n).symm ≪≫ (pullback f).mapIso α)
    (sectionKernelDifferenceOfCartesianSectionsIso f g s t s' t' hs ht)
    (differenceSheafBoundaryIso i' s'.ker t'.ker
      (avoids_sectionKernel_cartesianSections b i i' f g w s s' hs aD)
      (avoids_sectionKernel_cartesianSections b i i' f g w t t' ht aE))
    (pullbackBoundaryTrivialization b i i' f w M e)
  rw [sectionKernelDifferenceOfCartesianSectionsIso_boundary b i i' f g w s t s' t' hs ht aD aE]
  exact boundary_root_frame_pullback b i i' f w M (differenceSheaf s.ker t.ker) n α
    (differenceSheafBoundaryIso i s.ker t.ker aD aE) e he

end Stacks.AlgebraicGeometry.ModuleLimits
