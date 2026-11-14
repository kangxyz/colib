/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerIndexingResolutionUnit
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerIndexingPostcompose
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerForgetCocycle

/-!
# Actual coefficient-restriction resolution comparisons

Compare the exact restricted chosen resolution with the chosen integral resolution.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.HigherDirectImagePresheaf
universe u
attribute [local instance] HasDerivedCategory.standard
namespace Stacks.EtaleCohomology
variable (Λ : Type) [CommRing Λ] (X : Scheme.{u})

/-- Compare the exact restriction of the chosen Lambda resolution with the chosen Z resolution.
There is no assertion that restriction preserves injectives. -/
def kummerRestrictedResolutionComparison (M : EtaleModules.{u, 0} Λ X) :
    ((etaleModuleRestrictScalars (Int.castRingHom Λ) X).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (injectiveResolution M).cocomplex ⟶
    (injectiveResolution ((etaleModuleRestrictScalars (Int.castRingHom Λ) X).obj M)).cocomplex :=
  Classical.choose (Stacks.Cohomology.ModuleComparison.exists_mapResolutionComparison
    (etaleModuleRestrictScalars (Int.castRingHom Λ) X)
    (injectiveResolution M)
    (injectiveResolution ((etaleModuleRestrictScalars (Int.castRingHom Λ) X).obj M)))

/-- The actual chosen comparison extends the identity, not an assumed comparison isomorphism. -/
theorem kummerRestrictedResolutionComparison_augmentation (M : EtaleModules.{u, 0} Λ X) :
    (etaleModuleRestrictScalars (Int.castRingHom Λ) X).map
        ((injectiveResolution M).ι.f 0) ≫
      (kummerRestrictedResolutionComparison Λ X M).f 0 =
    (injectiveResolution ((etaleModuleRestrictScalars (Int.castRingHom Λ) X).obj M)).ι.f 0 :=
  Classical.choose_spec (Stacks.Cohomology.ModuleComparison.exists_mapResolutionComparison
    (etaleModuleRestrictScalars (Int.castRingHom Λ) X)
    (injectiveResolution M)
    (injectiveResolution ((etaleModuleRestrictScalars (Int.castRingHom Λ) X).obj M)))

/-- Read that same comparison in bounded-below homotopy complexes using the existing extension. -/
def kummerRestrictedResolutionPlus (M : EtaleModules.{u, 0} Λ X) :=
  Stacks.Cohomology.ModulePushforwardComparison.resolutionExtendPlusHom
    (etaleModuleRestrictScalars (Int.castRingHom Λ) X)
    (injectiveResolution M)
    (injectiveResolution ((etaleModuleRestrictScalars (Int.castRingHom Λ) X).obj M))
    (kummerRestrictedResolutionComparison Λ X M)

/-- The actual derived unit commutes with the actual comparison of the two resolutions. -/
theorem kummerRestrictedResolutionPlus_unit (M : EtaleModules.{u, 0} Λ X) :
    let T := etaleModuleRestrictScalars (Int.castRingHom Λ) X
    let G := etaleModuleGlobalSections.{u, 0} ℤ X
    let K := (HomotopyCategory.Plus.quotient (EtaleModules.{u, 0} Λ X)).obj
      (resolutionCochainPlus (injectiveResolution M))
    let L := (HomotopyCategory.Plus.quotient (EtaleModules.{u, 0} ℤ X)).obj
      (resolutionCochainPlus (injectiveResolution (T.obj M)))
    DerivedCategory.Plus.Qh.map
        (G.mapHomotopyCategoryPlus.map (kummerRestrictedResolutionPlus Λ X M)) ≫
      G.rightDerivedFunctorPlusUnith.app L =
    G.rightDerivedFunctorPlusUnith.app (T.mapHomotopyCategoryPlus.obj K) ≫
      G.rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Qh.map (kummerRestrictedResolutionPlus Λ X M)) :=
  (etaleModuleGlobalSections.{u, 0} ℤ X).rightDerivedFunctorPlusUnith.naturality
    (kummerRestrictedResolutionPlus Λ X M)

end Stacks.EtaleCohomology
end
