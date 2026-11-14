/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerCoefficientResolutionTransport
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerOriginalComparisonCocycle
public import StacksFrontier.Homology.DerivedIndexing.StandardComparison

/-!
# Original Ext comparison and the standard resolution homology model

Use the proved equality of the original indexing and standard comparison, rather
than silently exchanging the two. Read the actual restricted resolution map in homology.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.HigherDirectImagePresheaf
open Stacks.Cohomology.ModulePushforwardComparison
universe u
attribute [local instance] HasDerivedCategory.standard
namespace Stacks.EtaleCohomology
variable (Λ : Type) [CommRing Λ] (X : Scheme.{u})

/-- The indexing map of the original comparison is the existing standard resolution map. -/
theorem kummerOriginalIndexing_eq_standard (M : EtaleModules.{u, 0} Λ X) (n : ℕ) :
    (Stacks.DerivedIndexing.rightDerivedIso
      (etaleModuleGlobalSections.{u, 0} Λ X) n).inv.app M =
    (derivedPlusToStandard (etaleModuleGlobalSections.{u, 0} Λ X) n).hom.app M := by
  exact congrArg (fun f => f.app M)
    (Stacks.DerivedIndexing.rightDerivedIso_inv_eq
      (etaleModuleGlobalSections.{u, 0} Λ X) n)

/-- Explicit standard-model factors of the ORIGINAL Ext comparison. -/
theorem kummerOriginalExtComparison_standard_factors
    (M : EtaleModules.{u, 0} Λ X) (n : ℕ) :
    (etaleModuleRightDerivedPlusIsoExt Λ X M n).hom =
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map
        ((derivedPlusToStandard (etaleModuleGlobalSections.{u, 0} Λ X) n).hom.app M) ≫
      (Stacks.Cohomology.GlobalSections.extConstantModuleSheafIsoRightDerived
        Λ X.smallEtaleTopology n).inv.app M := by
  exact congrArg (fun f =>
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map f ≫
      (Stacks.Cohomology.GlobalSections.extConstantModuleSheafIsoRightDerived
        Λ X.smallEtaleTopology n).inv.app M)
    (kummerOriginalIndexing_eq_standard Λ X M n)

/-- Actual comparison of the chosen resolutions becomes the actual ordinary homology map. -/
theorem kummerRestrictedResolution_homology (M : EtaleModules.{u, 0} Λ X) (n : ℕ) :
    let T := etaleModuleRestrictScalars (Int.castRingHom Λ) X
    let H := etaleModuleGlobalSections.{u, 0} ℤ X
    let I := injectiveResolution M
    let J := injectiveResolution (T.obj M)
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ) (n : ℤ)).map
      (DerivedCategory.Plus.Qh.map
        (H.mapHomotopyCategoryPlus.map (kummerRestrictedResolutionPlus Λ X M))) ≫
      (extendedHomologyIso H J.cocomplex n).hom =
    (extendedHomologyIso (T ⋙ H) I.cocomplex n).hom ≫
      HomologicalComplex.homologyMap
        ((H.mapHomologicalComplex (ComplexShape.up ℕ)).map
          (kummerRestrictedResolutionComparison Λ X M)) n := by
  exact homologyFunctor_map_qh_resolutionExtendPlusHom
      (etaleModuleRestrictScalars (Int.castRingHom Λ) X)
      (etaleModuleGlobalSections.{u, 0} ℤ X)
      (injectiveResolution M)
      (injectiveResolution ((etaleModuleRestrictScalars (Int.castRingHom Λ) X).obj M))
      (kummerRestrictedResolutionComparison Λ X M) n

end Stacks.EtaleCohomology
end
