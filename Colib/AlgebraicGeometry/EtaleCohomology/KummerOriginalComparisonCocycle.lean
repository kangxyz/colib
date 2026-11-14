/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerDerivedUnitResolution
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerModuleComparisonNaturality
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.CocycleFormula

/-!
# Original Ext comparison on resolution cocycles

Retain the actual ordinary-derived and bounded-below indexing comparison factors.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open Opposite ModuleSheafCohomology
universe u
attribute [local instance] HasDerivedCategory.standard
private lemma appendFive {A : Type*} [Category* A]
    {V₀ V₁ V₂ V₃ V₄ V₅ V₆ V₇ V₈ : A}
    {p : V₀ ⟶ V₁} {e : V₁ ⟶ V₅}
    {a : V₀ ⟶ V₂} {b : V₂ ⟶ V₃} {c : V₃ ⟶ V₄}
    {d : V₄ ⟶ V₆} {f : V₆ ⟶ V₅}
    (h : p ≫ e = a ≫ b ≫ c ≫ d ≫ f) (x : V₅ ⟶ V₇) (y : V₇ ⟶ V₈) :
    p ≫ e ≫ x ≫ y = a ≫ b ≫ c ≫ d ≫ f ≫ x ≫ y := by
  rw [← Category.assoc p e, h]
  simp only [Category.assoc]

namespace Stacks.EtaleCohomology
variable (Λ : Type) [CommRing Λ] (X : Scheme.{u})

/-- Definitional factors of the original comparison, before any cocycle calculation. -/
theorem kummerOriginalComparison_inv_factors
    (M : EtaleModules.{u, 0} Λ X) (n : ℕ) :
    let G := etaleModuleGlobalSections.{u, 0} Λ X
    let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
    let C := Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology
    let α := Stacks.Cohomology.GlobalSections.moduleGlobalSectionsCorepresentation
      Λ X.smallEtaleTopology
    (etaleModuleRightDerivedPlusIsoExt Λ X M n).inv =
      (extFunctorObjIsoRightDerived (G ⋙ U) C α n).hom.app M ≫
        (Functor.rightDerivedCompIso G U n).hom.app M ≫
        U.map ((Stacks.DerivedIndexing.rightDerivedIso G n).hom.app M) := by
  exact Category.assoc _ _ _

/-- Read the original bounded-below comparison on the chosen injective resolution.
The ordinary-derived composition and original indexing factors remain explicit. -/
theorem kummerOriginalComparison_succ_cocycle
    (M : EtaleModules.{u, 0} Λ X) (n : ℕ)
    (hi : (ComplexShape.up ℕ).prev (n + 1) = n)
    (hk : (ComplexShape.up ℕ).next (n + 1) = n + 2) :
    (extLeftHomologyData (injectiveResolution M)
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology) n).π ≫
        (etaleModuleRightDerivedPlusIsoExt Λ X M (n + 1)).inv =
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
        1)).hom.app M) := by
  have h := Stacks.Cohomology.ModuleComparison.extFunctorObjIsoRightDerived_succ_π_comp
    ((etaleModuleGlobalSections.{u, 0} Λ X) ⋙ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u
        + 1})) (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology)
        (Stacks.Cohomology.GlobalSections.moduleGlobalSectionsCorepresentation
            Λ X.smallEtaleTopology) M n hi hk
  have hfactor := congrArg (fun f =>
    (extLeftHomologyData (injectiveResolution M)
      (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology) n).π ≫ f)
    (kummerOriginalComparison_inv_factors Λ X M (n + 1))
  exact hfactor.trans (appendFive h _ _)


end Stacks.EtaleCohomology
end
