/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerOriginalCocyclePath

/-! append the original middle map only after the source path and both
endpoints have been typed independently. No larger heartbeat limit is introduced. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open ModuleSheafCohomology
open Stacks.Cohomology.ModuleComparison
universe u
attribute [local instance] HasDerivedCategory.standard
private lemma appendRead {C : Type*} [Category C] {A B D E F : C}
    {p : A ⟶ B} {a : B ⟶ D} {r : A ⟶ D} {x : B ⟶ E} {z : E ⟶ F}
    {m : D ⟶ F} (hr : p ≫ a = r) (hc : x ≫ z = a ≫ m) :
    p ≫ x ≫ z = r ≫ m := by
  rw [hc, ← Category.assoc, hr]
namespace Stacks.EtaleCohomology
variable (Λ : Type) [CommRing Λ] (X : Scheme.{u})

/-- Original coefficient middle morphism with the Lambda source endpoint fixed. -/
def kummerIntegralCoefficientMiddle (M : EtaleModules.{u, 0} Λ X) (q : ℕ) :
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj
      (((etaleModuleGlobalSections.{u, 0} Λ X).rightDerivedPlus (q : ℤ)).obj M) ⟶
    (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).obj
      (((etaleModuleGlobalSections.{u, 0} ℤ X).rightDerivedPlus (q : ℤ)).obj
        ((etaleModuleRestrictScalars (Int.castRingHom Λ) X).obj M)) :=
  (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).map
    (rightDerivedPlusRestrictScalarsIso (Int.castRingHom Λ) X M q).hom

/-- Original integral coefficient comparison on cycles, with no expansion of the
long source path during the final composition elaboration. -/
theorem kummerIntegralCoefficient_cocycle_read (M : EtaleModules.{u, 0} Λ X) (n : ℕ)
    (hi : (ComplexShape.up ℕ).prev (n + 1) = n)
    (hk : (ComplexShape.up ℕ).next (n + 1) = n + 2) :
    (extLeftHomologyData (injectiveResolution M)
      (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology) n).π ≫
      (extConstantRestrictScalarsIso (Int.castRingHom Λ) X M (n + 1)).hom ≫
      (etaleModuleRightDerivedPlusIsoExt ℤ X
        ((etaleModuleRestrictScalars (Int.castRingHom Λ) X).obj M) (n + 1)).inv =
    kummerOriginalCocyclePath Λ X M n hi hk ≫
      kummerIntegralCoefficientMiddle Λ X M (n + 1) := by
  exact appendRead (kummerOriginalCocyclePath_eq Λ X M n hi hk)
    (kummerIntegralCoefficient_cancel_target Λ X M (n + 1))

end Stacks.EtaleCohomology
end
