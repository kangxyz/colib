/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerOriginalCocycleNormalized
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerIntegralResolutionCocycle

/-! # The actual map from Ext cocycles to global-section cycles

Name this map so the coefficient comparison can share its chosen-resolution type.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open HomologicalComplex Opposite ModuleSheafCohomology
open Stacks.Cohomology.HigherDirectImagePresheaf Stacks.DerivedIndexing
open Stacks.Cohomology.ModuleComparison
universe u
attribute [local instance] HasDerivedCategory.standard
private lemma readCycles {C : Type*} [Category C]
    {A B D E F G H : C} (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E)
    (d : E ⟶ F) (m : F ⟶ G) (n : E ⟶ G) (p : D ⟶ H)
    (t : H ⟶ G) (q : B ⟶ H) (r : A ⟶ H)
    (h₁ : d ≫ m = n) (h₂ : c ≫ n = p ≫ t) (h₃ : b ≫ p = q)
    (h₄ : a ≫ q = r) : (a ≫ b ≫ c ≫ d) ≫ m = r ≫ t := by
  simp only [Category.assoc]
  rw [h₁, h₂, ← Category.assoc b p, h₃, ← Category.assoc a q, h₄]

private lemma replaceRead {C : Type*} [Category C] {A B D E F G H I : C}
    (m : A ⟶ I) (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E)
    (p : E ⟶ F) (q : F ⟶ G) (r : G ⟶ I) (s : E ⟶ H) (t : H ⟶ G)
    (hm : m = a ≫ b ≫ c ≫ p ≫ q ≫ r) (he : p ≫ q = s ≫ t) :
    m = (a ≫ b ≫ c ≫ s) ≫ t ≫ r := by
  rw [hm]
  simp only [Category.assoc]
  rw [← Category.assoc p q, he, Category.assoc]

namespace Stacks.EtaleCohomology
variable (Λ : Type) [CommRing Λ] (X : Scheme.{u})

set_option maxHeartbeats 800000 in
-- The comparison elaborates the original chosen-resolution maps; keep this budget local.
set_option backward.isDefEq.respectTransparency false in
/-- A typed step in the original coefficient comparison. -/
private theorem succ_hs (M : EtaleModules.{u, 0} Λ X) (n : ℕ) :
  let G := etaleModuleGlobalSections.{u, 0} Λ X
  let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  let I := injectiveResolution M
  let C := Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology
  let α := Stacks.Cohomology.GlobalSections.moduleGlobalSectionsCorepresentation
    Λ X.smallEtaleTopology
  let E := extLeftHomologyData I C n
  let K := (G.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let hi : (ComplexShape.up ℕ).prev (n + 1) = n := by simp
  let hk : (ComplexShape.up ℕ).next (n + 1) = n + 2 := by simp
  let s := E.cyclesIso.inv ≫
    ((((preadditiveCoyoneda.obj (op C)).mapHomologicalComplex (.up ℕ)).obj
      I.cocomplex).cyclesIsoSc' n (n + 1) (n + 2) hi hk).inv ≫
    cyclesMap ((α.inv.mapHomologicalComplex (.up ℕ)).app I.cocomplex) (n + 1) ≫
    (mapExactCyclesIso U K (n + 1)).hom
  s ≫ U.map (K.iCycles (n + 1)) = E.i ≫ α.inv.app (I.cocomplex.X (n + 1)) := by
  intro G U I C α E K hi hk s
  exact readCycles _ _ _ _ _ _ _ _ _ _
    (mapExactCyclesIso_hom_iCycles U K (n + 1))
    (cyclesMap_i ((α.inv.mapHomologicalComplex (.up ℕ)).app I.cocomplex) (n + 1))
    (cyclesIsoSc'_inv_iCycles _ n (n + 1) (n + 2) hi hk)
    (ShortComplex.LeftHomologyData.cyclesIso_inv_comp_iCycles E)

/-- The actual corepresentation map from Ext cocycles to global-section cycles. -/
def originalCocycleToCycles (M : EtaleModules.{u, 0} Λ X) (n : ℕ) :
    let G := etaleModuleGlobalSections.{u, 0} Λ X
    let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
    let I := injectiveResolution M
    let C := Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology
    let K := (G.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
    (extLeftHomologyData I C n).K ⟶ U.obj (K.cycles (n + 1)) := by
  let G := etaleModuleGlobalSections.{u, 0} Λ X
  let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  let I := injectiveResolution M
  let C := Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology
  let α := Stacks.Cohomology.GlobalSections.moduleGlobalSectionsCorepresentation
    Λ X.smallEtaleTopology
  let K := (G.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let hi : (ComplexShape.up ℕ).prev (n + 1) = n := by simp
  let hk : (ComplexShape.up ℕ).next (n + 1) = n + 2 := by simp
  exact (extLeftHomologyData I C n).cyclesIso.inv ≫
    ((((preadditiveCoyoneda.obj (op C)).mapHomologicalComplex (.up ℕ)).obj
      I.cocomplex).cyclesIsoSc' n (n + 1) (n + 2) hi hk).inv ≫
    cyclesMap ((α.inv.mapHomologicalComplex (.up ℕ)).app I.cocomplex) (n + 1) ≫
    (mapExactCyclesIso U K (n + 1)).hom

set_option backward.isDefEq.respectTransparency false in
/-- Read the named actual cycle map through its cycle inclusion. -/
theorem originalCocycleToCycles_i (M : EtaleModules.{u, 0} Λ X) (n : ℕ) :
    let G := etaleModuleGlobalSections.{u, 0} Λ X
    let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
    let I := injectiveResolution M
    let C := Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology
    let α := Stacks.Cohomology.GlobalSections.moduleGlobalSectionsCorepresentation
      Λ X.smallEtaleTopology
    let K := (G.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
    originalCocycleToCycles Λ X M n ≫ U.map (K.iCycles (n + 1)) =
      (extLeftHomologyData I C n).i ≫ α.inv.app (I.cocomplex.X (n + 1)) := by
  exact succ_hs Λ X M n


set_option maxHeartbeats 800000 in
-- The comparison elaborates the original chosen-resolution maps; keep this budget local.
set_option backward.isDefEq.respectTransparency false in
/-- Read the original Ext cocycle comparison through the named global-section cycle map. -/
theorem kummerOriginalExtCocycle_read (M : EtaleModules.{u, 0} Λ X) (n : ℕ) :
  let G := etaleModuleGlobalSections.{u, 0} Λ X
  let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  let I := injectiveResolution M
  let C := Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology
  let E := extLeftHomologyData I C n
  let K := (G.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let N := derivedPlusResolutionHomologyIso G I (n + 1) ≪≫
    extendedHomologyIso G I.cocomplex (n + 1)
  let s := originalCocycleToCycles Λ X M n
  let z := (etaleModuleRightDerivedPlusIsoExt Λ X M (n + 1)).inv
  E.π ≫ z = s ≫ U.map (K.homologyπ (n + 1)) ≫ U.map N.inv := by
  intro G U I C E K N s z
  let hi : (ComplexShape.up ℕ).prev (n + 1) = n := by simp
  let hk : (ComplexShape.up ℕ).next (n + 1) = n + 2 := by simp
  have h := (kummerOriginalCocyclePath_eq Λ X M n hi hk).trans
    (kummerOriginalCocyclePath_normalized Λ X M n hi hk)
  exact replaceRead _ _ _ _ _ _ _ _ _ h
    (homologyπ_mapExactHomologyIso_hom U K (n + 1))


end Stacks.EtaleCohomology
end
