/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerIntegralCoefficientRead

/-! type the existing long source cocycle path separately, before appending
any integral coefficient map. The definition is its actual expanded cycles path. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
open ModuleSheafCohomology
open Stacks.Cohomology.ModuleComparison
universe u
attribute [local instance] HasDerivedCategory.standard
namespace Stacks.EtaleCohomology
variable (Λ : Type) [CommRing Λ] (X : Scheme.{u})

/-- The original expanded source cycles path with its endpoint fixed before composition. -/
def kummerOriginalCocyclePath (M : EtaleModules.{u, 0} Λ X) (n : ℕ)
    (hi : (ComplexShape.up ℕ).prev (n + 1) = n)
    (hk : (ComplexShape.up ℕ).next (n + 1) = n + 2) :
    (extLeftHomologyData (injectiveResolution M)
      (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology) n).K ⟶
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj
        (((etaleModuleGlobalSections.{u, 0} Λ X).rightDerivedPlus ((n + 1 : ℕ) : ℤ)).obj M) :=
      (extLeftHomologyData (injectiveResolution M)
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology)
        n).cyclesIso.inv ≫
        ((((preadditiveCoyoneda.obj (op (Stacks.Cohomology.GlobalSections.constantModuleSheaf
        Λ X.smallEtaleTopology))).mapHomologicalComplex (ComplexShape.up ℕ)).obj
            (injectiveResolution M).cocomplex).cyclesIsoSc' n (n + 1) (n + 2) hi hk).inv ≫
        HomologicalComplex.cyclesMap
          ((NatTrans.mapHomologicalComplex
        (Stacks.Cohomology.GlobalSections.moduleGlobalSectionsCorepresentation
            Λ X.smallEtaleTopology).inv (ComplexShape.up ℕ)).app
            (injectiveResolution M).cocomplex) (n + 1) ≫
        ((((etaleModuleGlobalSections.{u, 0} Λ X) ⋙ (forget₂ (ModuleCat.{u + 1} Λ)
        AddCommGrpCat.{u + 1})).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (injectiveResolution M).cocomplex).homologyπ (n + 1) ≫
        ((injectiveResolution M).isoRightDerivedObj ((etaleModuleGlobalSections.{u, 0} Λ X) ⋙
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})) (n + 1)).inv ≫
        (Functor.rightDerivedCompIso (etaleModuleGlobalSections.{u, 0} Λ X) (forget₂
        (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) (n + 1)).hom.app M ≫
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map
        ((Stacks.DerivedIndexing.rightDerivedIso (etaleModuleGlobalSections.{u, 0} Λ X) (n +
        1)).hom.app M)

/-- This explicitly typed path is the verified original comparison on cycles. -/
theorem kummerOriginalCocyclePath_eq (M : EtaleModules.{u, 0} Λ X) (n : ℕ)
    (hi : (ComplexShape.up ℕ).prev (n + 1) = n)
    (hk : (ComplexShape.up ℕ).next (n + 1) = n + 2) :
    (extLeftHomologyData (injectiveResolution M)
      (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology) n).π ≫
      (etaleModuleRightDerivedPlusIsoExt Λ X M (n + 1)).inv =
      kummerOriginalCocyclePath Λ X M n hi hk := by
  exact kummerOriginalComparison_succ_cocycle Λ X M n hi hk

end Stacks.EtaleCohomology
end
