/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerTargetAugmentation

/-!
# Original named single-object comparison

Compare the actual homotopy lifts through their faithful inclusion,
then identify the existing natural and object-level single comparisons. These are
specific named morphisms; no Ext equivalence equality is assumed.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.ModulePushforwardComparison
universe u
attribute [local instance] HasDerivedCategory.standard
private lemma cancelIsoRight {C : Type*} [Category C] {A B D : C}
    (i : B ≅ D) {f : A ⟶ B} {g : A ⟶ D} (h : f ≫ i.hom = g) :
    f = g ≫ i.inv := by
  rw [← h]
  simp
namespace Stacks.EtaleCohomology
variable (Λ : Type) [CommRing Λ] (X : Scheme.{u})
local instance : IsIso
    (etaleModuleRestrictScalars (Int.castRingHom Λ) X).rightDerivedFunctorPlusUnith :=
  Functor.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
    (etaleModuleRestrictScalars (Int.castRingHom Λ) X)

set_option backward.isDefEq.respectTransparency false in
/-- The two actual single-complex lifts are equal by faithfulness, not by their names. -/
theorem kummerSingleMapPlus_eq_named (M : EtaleModules.{u, 0} Λ X) :
    singleMapPlusHom (etaleModuleRestrictScalars (Int.castRingHom Λ) X) M =
      ((etaleModuleRestrictScalars (Int.castRingHom Λ) X).mapHomotopyCategoryPlusObjSingleIso
        0 M).hom := by
  apply (HomotopyCategory.Plus.ι (EtaleModules.{u, 0} ℤ X)).map_injective
  rw [ι_map_singleMapPlusHom, mapHomotopyCategorySingleFunctor_hom_app]
  symm
  exact (HomotopyCategory.Plus.ι (EtaleModules.{u, 0} ℤ X)).map_preimage _

/-- The actual natural single-to-derived comparison has the named object's formula. -/
theorem kummerMapSingleFunctor_named (M : EtaleModules.{u, 0} Λ X) :
    let T := etaleModuleRestrictScalars (Int.castRingHom Λ) X
    (Functor.mapSingleFunctorCompQhIso T).hom.app M =
      DerivedCategory.Plus.Qh.map (T.mapHomotopyCategoryPlusObjSingleIso 0 M).hom ≫
        (Functor.singleFunctorPlusIsoCompQh (A := EtaleModules.{u, 0} ℤ X) 0).inv.app
          (T.obj M) := by
  have h := mapSingleFunctorCompQhIso_hom_app_comp
    (etaleModuleRestrictScalars (Int.castRingHom Λ) X) M
  rw [kummerSingleMapPlus_eq_named Λ X M] at h
  exact cancelIsoRight
    ((Functor.singleFunctorPlusIsoCompQh (A := EtaleModules.{u, 0} ℤ X) 0).app
      ((etaleModuleRestrictScalars (Int.castRingHom Λ) X).obj M)) h

/-- Identify the existing object-level right-derived single iso with the existing
natural single iso at this object, including actual inverse-unit components. -/
theorem kummerRightDerivedSingle_named (M : EtaleModules.{u, 0} Λ X) :
    let T := etaleModuleRestrictScalars (Int.castRingHom Λ) X
    (T.rightDerivedFunctorPlusObjSingleIso M).hom =
      (singleFunctorPlusRightDerivedIso T).hom.app M := by
  let T := etaleModuleRestrictScalars (Int.castRingHom Λ) X
  have : IsIso T.rightDerivedFunctorPlusUnith :=
    Functor.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology T
  have : IsIso (T.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.singleFunctor (EtaleModules.{u, 0} Λ X) 0).obj M)) :=
    NatIso.isIso_app_of_isIso T.rightDerivedFunctorPlusUnith _
  change T.rightDerivedFunctorPlus.map
      ((Functor.singleFunctorPlusIsoCompQh (A := EtaleModules.{u, 0} Λ X) 0).hom.app M) ≫
      inv (T.rightDerivedFunctorPlusUnith.app
        ((HomotopyCategory.Plus.singleFunctor (EtaleModules.{u, 0} Λ X) 0).obj M)) ≫
      DerivedCategory.Plus.Qh.map (T.mapHomotopyCategoryPlusObjSingleIso 0 M).hom ≫
      (Functor.singleFunctorPlusIsoCompQh (A := EtaleModules.{u, 0} ℤ X) 0).inv.app (T.obj M) =
    T.rightDerivedFunctorPlus.map
      ((Functor.singleFunctorPlusIsoCompQh (A := EtaleModules.{u, 0} Λ X) 0).hom.app M) ≫
      (asIso T.rightDerivedFunctorPlusUnith).inv.app
        ((HomotopyCategory.Plus.singleFunctor (EtaleModules.{u, 0} Λ X) 0).obj M) ≫
      (Functor.mapSingleFunctorCompQhIso T).hom.app M
  rw [asIso_inv, NatIso.isIso_inv_app, kummerMapSingleFunctor_named Λ X M]

/-- The exact named single-object comparison contains precisely the previously
retained actual single-comparison factors. -/
theorem kummerExactSingle_named (M : EtaleModules.{u, 0} Λ X) :
    let T := etaleModuleRestrictScalars (Int.castRingHom Λ) X
    (T.mapDerivedCategoryPlusObjSingleIso M).hom =
      (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus T).inv.app
        ((DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} Λ X) 0).obj M) ≫
      (singleFunctorPlusRightDerivedIso T).hom.app M := by
  change _ ≫ (Functor.rightDerivedFunctorPlusObjSingleIso
    (etaleModuleRestrictScalars (Int.castRingHom Λ) X) M).hom = _
  rw [kummerRightDerivedSingle_named Λ X M]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Target augmentation expressed using the ACTUAL original named exact-single iso. -/
theorem kummerTargetAugmentation_named (M : EtaleModules.{u, 0} Λ X) :
    let T := etaleModuleRestrictScalars (Int.castRingHom Λ) X
    let a := (Stacks.DerivedIndexing.singleIsoResPlusQh
      (C := EtaleModules.{u, 0} Λ X)).app M
    let b := (Stacks.DerivedIndexing.singleIsoResPlusQh
      (C := EtaleModules.{u, 0} ℤ X)).app (T.obj M)
    T.mapDerivedCategoryPlus.map a.inv ≫ (T.mapDerivedCategoryPlusObjSingleIso M).hom ≫
      b.hom = T.mapDerivedCategoryPlusFactorsh.hom.app (Stacks.DerivedIndexing.resPlus.obj M) ≫
      DerivedCategory.Plus.Qh.map (kummerRestrictedResolutionPlus Λ X M) := by
  dsimp only
  rw [kummerExactSingle_named Λ X M, Category.assoc]
  exact kummerTargetAugmentation_exactFactors Λ X M

end Stacks.EtaleCohomology
end
