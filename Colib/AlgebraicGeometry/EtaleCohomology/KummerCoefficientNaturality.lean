/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleRestrictScalarsCohomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryPlusNatTransSingle

/-!
# Naturality of the original coefficient-change comparison

The derived and Ext coefficient comparisons used by Kummer module classes are
natural in their coefficient. No cross-space pushforward compatibility is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
universe u
attribute [local instance] HasDerivedCategory.standard
namespace Stacks.EtaleCohomology
variable {Λ : Type} [CommRing Λ] (Y : Scheme.{u})

private theorem derivedExt_naturality (Λ : Type) [CommRing Λ] {Y : Scheme.{u}}
    {M M' : EtaleModules.{u, 0} Λ Y} (h : M ⟶ M') (i : ℕ) :
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map
        (((etaleModuleGlobalSections.{u, 0} Λ Y).rightDerivedPlus (i : ℤ)).map h) ≫
        (etaleModuleRightDerivedPlusIsoExt Λ Y M' i).hom =
      (etaleModuleRightDerivedPlusIsoExt Λ Y M i).hom ≫
        (extFunctorObj (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ
          Y.smallEtaleTopology) i).map h := by
  have n4 := (Stacks.DerivedIndexing.rightDerivedIso
    (etaleModuleGlobalSections.{u, 0} Λ Y) i).inv.naturality h
  have n5 := (Stacks.Cohomology.GlobalSections.extConstantModuleSheafIsoRightDerived Λ
    Y.smallEtaleTopology i).inv.naturality h
  dsimp only [Functor.comp_map] at n5
  dsimp only [etaleModuleRightDerivedPlusIsoExt, Iso.trans, Iso.symm, Functor.mapIso, Iso.app]
  rw [← Functor.map_comp_assoc, n4, Functor.map_comp_assoc, n5, Category.assoc]


/-- Naturality for the *existing* derived comparison, not a replacement equivalence. -/
theorem kummerRightDerivedPlusRestrictScalarsIso_hom_naturality {N N' : EtaleModules.{u, 0} Λ Y}
    (g : N ⟶ N') (i : ℤ) :
    (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)).map
        (((etaleModuleGlobalSections.{u, 0} Λ Y).rightDerivedPlus i).map g) ≫
      (rightDerivedPlusRestrictScalarsIso (Int.castRingHom Λ) Y N' i).hom =
    (rightDerivedPlusRestrictScalarsIso (Int.castRingHom Λ) Y N i).hom ≫
      ((etaleModuleGlobalSections.{u, 0} ℤ Y).rightDerivedPlus i).map
        ((etaleModuleRestrictScalars (Int.castRingHom Λ) Y).map g) := by
  have h1 := ((ModuleCat.restrictScalars.{u + 1}
    (Int.castRingHom Λ)).mapDerivedCategoryHomologyIso i).inv.naturality
    (DerivedCategory.Plus.ι.map ((etaleModuleDerivedGlobalSections.{u, 0} Λ Y).map
      ((DerivedCategory.Plus.singleFunctor _ 0).map g)))
  have h2 := (etaleModuleDerivedGlobalSectionsRestrictScalars (Int.castRingHom Λ) Y).hom.naturality
    ((DerivedCategory.Plus.singleFunctor _ 0).map g)
  have h3 := Stacks.DerivedFunctor.mapDerivedCategoryPlusObjSingleIso_hom_naturality
    (S := etaleModuleRestrictScalars (Int.castRingHom Λ) Y) g
  have hmain : (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} ℤ) i).map
        ((ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)).mapDerivedCategory.map
          (DerivedCategory.Plus.ι.map ((etaleModuleDerivedGlobalSections.{u, 0} Λ Y).map
            ((DerivedCategory.Plus.singleFunctor _ 0).map g)))) ≫
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ) i).map
        ((etaleModuleDerivedGlobalSectionsRestrictScalars (Int.castRingHom Λ) Y).hom.app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj N') ≫
        (etaleModuleDerivedGlobalSections.{u, 0} ℤ Y).map
          ((etaleModuleRestrictScalars (Int.castRingHom Λ) Y).mapDerivedCategoryPlusObjSingleIso
            N').hom) =
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ) i).map
        ((etaleModuleDerivedGlobalSectionsRestrictScalars (Int.castRingHom Λ) Y).hom.app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj N) ≫
        (etaleModuleDerivedGlobalSections.{u, 0} ℤ Y).map
          ((etaleModuleRestrictScalars (Int.castRingHom Λ) Y).mapDerivedCategoryPlusObjSingleIso
            N).hom) ≫
      ((etaleModuleGlobalSections.{u, 0} ℤ Y).rightDerivedPlus i).map
        ((etaleModuleRestrictScalars (Int.castRingHom Λ) Y).map g) := by
    change (DerivedCategory.Plus.homologyFunctor _ i).map
        ((ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)).mapDerivedCategoryPlus.map
          ((etaleModuleDerivedGlobalSections.{u, 0} Λ Y).map
            ((DerivedCategory.Plus.singleFunctor _ 0).map g))) ≫ _ =
      _ ≫ (DerivedCategory.Plus.homologyFunctor _ i).map
        ((etaleModuleDerivedGlobalSections.{u, 0} ℤ Y).map
          ((DerivedCategory.Plus.singleFunctor _ 0).map
            ((etaleModuleRestrictScalars (Int.castRingHom Λ) Y).map g)))
    simp only [← Functor.map_comp]
    refine congrArg _ ?_
    rw [reassoc_of% h2, ← Functor.map_comp, h3, Functor.map_comp, Category.assoc]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h1).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hmain).trans (Category.assoc _ _ _).symm)))

set_option backward.isDefEq.respectTransparency false in
/-- The original Ext coefficient-change comparison is natural in module coefficients.
Proof candidate: paste the two derived/Ext squares with the preceding derived
coefficient square. The expression is the existing extConstantRestrictScalarsIso. -/
theorem kummerExtConstantRestrictScalarsIso_hom_naturality
    {M M' : EtaleModules.{u, 0} Λ Y} (φ : M ⟶ M') (i : ℕ) :
    (extFunctorObj (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ
      Y.smallEtaleTopology) i).map φ ≫
        (extConstantRestrictScalarsIso (Int.castRingHom Λ) Y M' i).hom =
    (extConstantRestrictScalarsIso (Int.castRingHom Λ) Y M i).hom ≫
      (extFunctorObj (Stacks.Cohomology.GlobalSections.constantModuleSheaf ℤ
        Y.smallEtaleTopology) i).map
          ((etaleModuleRestrictScalars (Int.castRingHom Λ) Y).map φ) := by
  have hA := derivedExt_naturality Λ φ i
  have hB := derivedExt_naturality ℤ
    ((etaleModuleRestrictScalars (Int.castRingHom Λ) Y).map φ) i
  have hR := congrArg (fun f =>
    (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).map f)
      (kummerRightDerivedPlusRestrictScalarsIso_hom_naturality Y φ (i : ℤ))
  simp only [Functor.map_comp] at hR
  dsimp only [extConstantRestrictScalarsIso, Iso.trans_hom,
    Iso.symm_hom, Functor.mapIso_hom, Iso.refl_hom]
  -- Cancel the source derived/Ext isomorphism, then paste the three actual squares.
  apply (cancel_epi (etaleModuleRightDerivedPlusIsoExt Λ Y M i).hom).1
  simp only [Category.assoc]
  rw [← reassoc_of% hA]
  simp only [Iso.hom_inv_id_assoc, Category.id_comp]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ (etaleModuleRightDerivedPlusIsoExt ℤ Y
      ((etaleModuleRestrictScalars (Int.castRingHom Λ) Y).obj M') i).hom) hR).trans
      ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hB)))

end Stacks.EtaleCohomology
end
