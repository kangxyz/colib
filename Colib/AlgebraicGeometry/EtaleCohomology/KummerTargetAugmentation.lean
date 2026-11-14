/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerCoefficientAugmentation
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerCoefficientResolutionHomology

/-!
# Actual chosen restriction comparison and original target augmentation

Convert the existing resolution transport theorem using the proved
identification of resolutionDerivedIso with original singleIsoResPlusQh. Then expose
the exact-functor comparison factors; do not assume a final Ext comparison identity.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.HigherDirectImagePresheaf
open Stacks.Cohomology.ModulePushforwardComparison
universe u
attribute [local instance] HasDerivedCategory.standard

private lemma exactUnitPaste {C : Type*} [Category C]
    {A B D E F G H : C} (u : A ≅ B) (eB : B ≅ D) (eE : E ≅ F)
    {a : D ⟶ F} {b : B ⟶ E} {s : E ⟶ G} {j : G ⟶ H}
    {c : A ⟶ H} {f : D ⟶ A}
    (hc : u.hom ≫ b ≫ s ≫ j = c)
    (hn : a ≫ eE.inv = eB.inv ≫ b) (hf : eB.inv ≫ u.inv = f) :
    a ≫ eE.inv ≫ s ≫ j = f ≫ c := by
  rw [← Category.assoc a eE.inv, hn, ← hf, ← hc]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

namespace Stacks.EtaleCohomology
variable (Λ : Type) [CommRing Λ] (X : Scheme.{u})
local instance : IsIso
    (etaleModuleRestrictScalars (Int.castRingHom Λ) X).rightDerivedFunctorPlusUnith :=
  Functor.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
    (etaleModuleRestrictScalars (Int.castRingHom Λ) X)

set_option backward.isDefEq.respectTransparency false in
/-- Actual chosen complex comparison, with BOTH resolution identifications changed
using the proved equality to the original indexing augmentation. -/
theorem kummerTargetAugmentation_rightDerived (M : EtaleModules.{u, 0} Λ X) :
    let T := etaleModuleRestrictScalars (Int.castRingHom Λ) X
    let K := Stacks.DerivedIndexing.resPlus.obj M
    let a := (Stacks.DerivedIndexing.singleIsoResPlusQh
      (C := EtaleModules.{u, 0} Λ X)).app M
    let b := (Stacks.DerivedIndexing.singleIsoResPlusQh
      (C := EtaleModules.{u, 0} ℤ X)).app (T.obj M)
    T.rightDerivedFunctorPlusUnith.app K ≫ T.rightDerivedFunctorPlus.map a.inv ≫
      (singleFunctorPlusRightDerivedIso T).hom.app M ≫ b.hom =
    DerivedCategory.Plus.Qh.map (kummerRestrictedResolutionPlus Λ X M) := by
  let T := etaleModuleRestrictScalars (Int.castRingHom Λ) X
  have : IsIso T.rightDerivedFunctorPlusUnith :=
    Functor.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology T
  have ha : resolutionDerivedIso (injectiveResolution M) =
      (Stacks.DerivedIndexing.singleIsoResPlusQh
        (C := EtaleModules.{u, 0} Λ X)).app M :=
    Iso.ext (Stacks.DerivedIndexing.resolutionDerivedIso_hom_eq M)
  have hb : resolutionDerivedIso (injectiveResolution (T.obj M)) =
      (Stacks.DerivedIndexing.singleIsoResPlusQh
        (C := EtaleModules.{u, 0} ℤ X)).app (T.obj M) :=
    Iso.ext (Stacks.DerivedIndexing.resolutionDerivedIso_hom_eq (T.obj M))
  have h := rightDerivedFunctorPlusUnit_comp_singleFunctorIso_eq T
    (injectiveResolution M) (injectiveResolution (T.obj M))
    (kummerRestrictedResolutionComparison Λ X M)
    (kummerRestrictedResolutionComparison_augmentation Λ X M)
  rw [ha, hb] at h
  exact h

/-- Exact restriction transport with the original single-comparison factor explicit.
Identifying this factor with the named exact-single iso is a separate wrapper step. -/
theorem kummerTargetAugmentation_exactFactors (M : EtaleModules.{u, 0} Λ X) :
    let T := etaleModuleRestrictScalars (Int.castRingHom Λ) X
    let K := Stacks.DerivedIndexing.resPlus.obj M
    let a := (Stacks.DerivedIndexing.singleIsoResPlusQh
      (C := EtaleModules.{u, 0} Λ X)).app M
    let b := (Stacks.DerivedIndexing.singleIsoResPlusQh
      (C := EtaleModules.{u, 0} ℤ X)).app (T.obj M)
    T.mapDerivedCategoryPlus.map a.inv ≫
      (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus T).inv.app
        ((DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} Λ X) 0).obj M) ≫
      (singleFunctorPlusRightDerivedIso T).hom.app M ≫ b.hom =
    T.mapDerivedCategoryPlusFactorsh.hom.app K ≫
      DerivedCategory.Plus.Qh.map (kummerRestrictedResolutionPlus Λ X M) := by
  let T := etaleModuleRestrictScalars (Int.castRingHom Λ) X
  let K := Stacks.DerivedIndexing.resPlus.obj M
  let a := (Stacks.DerivedIndexing.singleIsoResPlusQh
    (C := EtaleModules.{u, 0} Λ X)).app M
  let e := Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus T
  have : IsIso T.rightDerivedFunctorPlusUnith :=
    Functor.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology T
  have : IsIso (T.rightDerivedFunctorPlusUnith.app K) :=
    NatIso.isIso_app_of_isIso T.rightDerivedFunctorPlusUnith K
  exact exactUnitPaste (asIso (T.rightDerivedFunctorPlusUnith.app K))
    (e.app (DerivedCategory.Plus.Qh.obj K))
    (e.app ((DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} Λ X) 0).obj M))
    (kummerTargetAugmentation_rightDerived Λ X M)
    (e.inv.naturality a.inv)
    (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus_inv_app_comp_inv_unit T K)

end Stacks.EtaleCohomology
end
