/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerRestrictedResolution

/-!
# Identification of the actual resolution models

Compare the chosen extended resolution and its actual augmentations.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.HigherDirectImagePresheaf
open Stacks.Cohomology.ModulePushforwardComparison
universe u
attribute [local instance] HasDerivedCategory.standard
namespace Stacks.EtaleCohomology
variable (Λ : Type) [CommRing Λ] (X : Scheme.{u})

/-- The original indexing resolution and the explicit cochain resolution are the same model. -/
theorem kummerResPlus_eq_resolutionCochainPlus (M : EtaleModules.{u, 0} Λ X) :
    Stacks.DerivedIndexing.resPlus.obj M =
      (HomotopyCategory.Plus.quotient (EtaleModules.{u, 0} Λ X)).obj
        (resolutionCochainPlus (injectiveResolution M)) := by
  rfl

/-- The explicit extension augmentation is the original extended-resolution augmentation. -/
theorem kummerResolutionSingleHom_eq_augmentation (M : EtaleModules.{u, 0} Λ X) :
    resolutionSingleHom (injectiveResolution M) = (injectiveResolution M).ι' := by
  rfl

/-- The original resUnit is the quotient of the explicit extension augmentation. -/
theorem kummerResUnit_eq_resolutionSingleHom (M : EtaleModules.{u, 0} Λ X) :
    Stacks.DerivedIndexing.resUnit.app M =
      (HomotopyCategory.quotient (EtaleModules.{u, 0} Λ X) (ComplexShape.up ℤ)).map
        (resolutionSingleHom (injectiveResolution M)) := by
  rfl

/-- The actual restricted resolution comparison respects original extended augmentations. -/
theorem kummerRestrictedResolution_original_augmentation (M : EtaleModules.{u, 0} Λ X) :
    let T := etaleModuleRestrictScalars (Int.castRingHom Λ) X
    (HomologicalComplex.singleMapHomologicalComplex T (ComplexShape.up ℤ) 0).hom.app M ≫
        (injectiveResolution (T.obj M)).ι' =
      (T.mapHomologicalComplex (ComplexShape.up ℤ)).map (injectiveResolution M).ι' ≫
        Stacks.Cohomology.ModulePushforwardComparison.resolutionExtendComparison T
          (injectiveResolution M) (injectiveResolution (T.obj M))
          (kummerRestrictedResolutionComparison Λ X M) := by
  exact singleMapHomologicalComplex_comp_resolutionSingleHom
      (etaleModuleRestrictScalars (Int.castRingHom Λ) X)
      (injectiveResolution M)
      (injectiveResolution ((etaleModuleRestrictScalars (Int.castRingHom Λ) X).obj M))
      (kummerRestrictedResolutionComparison Λ X M)
      (kummerRestrictedResolutionComparison_augmentation Λ X M)

end Stacks.EtaleCohomology
end
