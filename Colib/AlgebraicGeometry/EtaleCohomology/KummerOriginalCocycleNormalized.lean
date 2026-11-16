/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerTermwiseExtendedAssembly
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerOriginalCocyclePath
public import StacksFrontier.Homology.CompositeCollapseResolution

/-! # Original positive-degree cocycle reading through its resolution normalization

The maps are the original indexing and chosen-resolution maps.
No equality of the two Ext equivalences is assumed.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex Opposite
open Stacks.Cohomology.HigherDirectImagePresheaf Stacks.DerivedIndexing
open ModuleSheafCohomology Stacks.Cohomology.ModuleComparison
universe u
attribute [local instance] HasDerivedCategory.standard
private lemma composeRead {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B E : C} {V W : D} (a : V ⟶ W) (b : W ⟶ F.obj B)
    (d : V ⟶ F.obj A) (c : A ⟶ B) (e : B ⟶ E) (f : A ⟶ E)
    (hp : a ≫ b = d ≫ F.map c) (hn : c ≫ e = f) :
    a ≫ b ≫ F.map e = d ≫ F.map f := by
  rw [← Category.assoc, hp, Category.assoc, ← F.map_comp, hn]

namespace Stacks.EtaleCohomology
variable (Λ : Type) [CommRing Λ] (X : Scheme.{u})

set_option maxHeartbeats 800000 in
-- Checking the original expanded cocycle path against its resolution model unfolds several
-- derived-functor comparison definitions; keep this larger budget local to that identification.
set_option backward.isDefEq.respectTransparency false in
/-- Read the actual original source path using the original chosen-resolution normalizer. -/
theorem kummerOriginalCocyclePath_normalized
    (M : EtaleModules.{u, 0} Λ X) (n : ℕ)
    (hi : (ComplexShape.up ℕ).prev (n + 1) = n)
    (hk : (ComplexShape.up ℕ).next (n + 1) = n + 2) :
    let G := etaleModuleGlobalSections.{u, 0} Λ X
    let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
    let I := injectiveResolution M
    let C := Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology
    let α := Stacks.Cohomology.GlobalSections.moduleGlobalSectionsCorepresentation
      Λ X.smallEtaleTopology
    let N := derivedPlusResolutionHomologyIso G I (n + 1) ≪≫
      extendedHomologyIso G I.cocomplex (n + 1)
    kummerOriginalCocyclePath Λ X M n hi hk =
      (extLeftHomologyData I C n).cyclesIso.inv ≫
        ((((preadditiveCoyoneda.obj (op C)).mapHomologicalComplex (.up ℕ)).obj
          I.cocomplex).cyclesIsoSc' n (n + 1) (n + 2) hi hk).inv ≫
        cyclesMap ((α.inv.mapHomologicalComplex (.up ℕ)).app I.cocomplex) (n + 1) ≫
        (((G ⋙ U).mapHomologicalComplex (.up ℕ)).obj I.cocomplex).homologyπ (n + 1) ≫
        (mapExactHomologyIso U ((G.mapHomologicalComplex (.up ℕ)).obj I.cocomplex)
          (n + 1)).hom ≫ U.map N.inv := by
  let G := etaleModuleGlobalSections.{u, 0} Λ X
  let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  let I := injectiveResolution M
  let N := derivedPlusResolutionHomologyIso G I (n + 1) ≪≫
    extendedHomologyIso G I.cocomplex (n + 1)
  have hn : ((rightDerivedIso G (n + 1)).app M).symm ≪≫
      I.isoRightDerivedObj G (n + 1) = N := by
    apply Iso.ext
    exact kummerSourceIndexing_normalization Λ X M (n + 1)
  have hni : (I.isoRightDerivedObj G (n + 1)).inv ≫
      (rightDerivedIso G (n + 1)).hom.app M = N.inv :=
    congrArg Iso.inv hn
  have hp := Stacks.RightDerivedComp.isoRightDerivedObj_inv_comp_rightDerivedCompIso_hom_app
    G U (n + 1) M
  have ht : (I.isoRightDerivedObj (G ⋙ U) (n + 1)).inv ≫
      (Functor.rightDerivedCompIso G U (n + 1)).hom.app M ≫
      U.map ((rightDerivedIso G (n + 1)).hom.app M) =
    (mapExactHomologyIso U ((G.mapHomologicalComplex (.up ℕ)).obj I.cocomplex)
      (n + 1)).hom ≫ U.map N.inv := by
    exact composeRead U _ _ _ _ _ _ hp hni
  let C := Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology
  let α := Stacks.Cohomology.GlobalSections.moduleGlobalSectionsCorepresentation
    Λ X.smallEtaleTopology
  exact congrArg (fun z => (extLeftHomologyData I C n).cyclesIso.inv ≫
    ((((preadditiveCoyoneda.obj (op C)).mapHomologicalComplex (.up ℕ)).obj
      I.cocomplex).cyclesIsoSc' n (n + 1) (n + 2) hi hk).inv ≫
    cyclesMap ((α.inv.mapHomologicalComplex (.up ℕ)).app I.cocomplex) (n + 1) ≫
    (((G ⋙ U).mapHomologicalComplex (.up ℕ)).obj I.cocomplex).homologyπ (n + 1) ≫ z) ht

end Stacks.EtaleCohomology
end
