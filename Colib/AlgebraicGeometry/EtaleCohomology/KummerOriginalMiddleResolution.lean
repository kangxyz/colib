/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerExactCoefficientHomology

/-!
# Original coefficient middle followed by actual target normalization

This keeps the original named rightDerivedPlusRestrictScalarsIso.
It does not prove the final Ext equivalence or its degree-zero specialization.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.HigherDirectImagePresheaf
universe u
attribute [local instance] HasDerivedCategory.standard

private lemma mapFourPaste {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B E H I : C} (a : A ⟶ B) (b : B ⟶ E) (c : E ⟶ H) (d : H ⟶ I)
    {V : D} (x : V ⟶ F.obj A) :
    (x ≫ F.map (a ≫ b)) ≫ F.map (c ≫ d) =
      x ≫ F.map (a ≫ b ≫ c ≫ d) := by
  simp only [Functor.map_comp, Category.assoc]

namespace Stacks.EtaleCohomology
variable (Λ : Type) [CommRing Λ] (X : Scheme.{u})

set_option backward.isDefEq.respectTransparency false in
/-- Actual original coefficient middle, followed by actual original target resolution
normalization, is precisely the previously verified single-to-resolution arrow. -/
theorem kummerOriginalMiddle_target_normalization
    (M : EtaleModules.{u, 0} Λ X) (q : ℕ) :
    let T := etaleModuleRestrictScalars (Int.castRingHom Λ) X
    let H := etaleModuleGlobalSections.{u, 0} ℤ X
    let R := ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)
    let D := DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ) (q : ℤ)
    (rightDerivedPlusRestrictScalarsIso (Int.castRingHom Λ) X M q).hom ≫
      (derivedPlusResolutionHomologyIso H (injectiveResolution (T.obj M)) q).hom =
    (Stacks.ExactDerivedPlus.mapDerivedCategoryPlusHomologyIso R (q : ℤ)
      ((etaleModuleGlobalSections.{u, 0} Λ X).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} Λ X) 0).obj M))).inv ≫
      D.map (kummerCoefficientSingleResolutionLeft Λ X M) := by
  dsimp only
  rw [kummerSourceNormalization_factors ℤ X]
  dsimp only [rightDerivedPlusRestrictScalarsIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom]
  exact mapFourPaste _ _ _ _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- Paste the original middle with the verified chosen-resolution homology formula.
The remaining source exact-homology/corepresentation factors are still explicit. -/
theorem kummerOriginalMiddle_resolution_homology
    (M : EtaleModules.{u, 0} Λ X) (q : ℕ) :
    let T := etaleModuleRestrictScalars (Int.castRingHom Λ) X
    let H := etaleModuleGlobalSections.{u, 0} ℤ X
    let R := ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)
    let D := DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ) (q : ℤ)
    let E := (Stacks.ExactDerivedPlus.mapDerivedCategoryPlusHomologyIso R (q : ℤ)
      ((etaleModuleGlobalSections.{u, 0} Λ X).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} Λ X) 0).obj M))).inv
    (rightDerivedPlusRestrictScalarsIso (Int.castRingHom Λ) X M q).hom ≫
      (derivedPlusResolutionHomologyIso H (injectiveResolution (T.obj M)) q).hom ≫
      (extendedHomologyIso H (injectiveResolution (T.obj M)).cocomplex q).hom =
    E ≫ D.map (kummerCoefficientSourceAugmentation Λ X M) ≫
      D.map (kummerCoefficientResolutionPrefix Λ X M) ≫
      (extendedHomologyIso (T ⋙ H) (injectiveResolution M).cocomplex q).hom ≫
      HomologicalComplex.homologyMap
        ((H.mapHomologicalComplex (ComplexShape.up ℕ)).map
          (kummerRestrictedResolutionComparison Λ X M)) q := by
  dsimp only
  rw [← Category.assoc, kummerOriginalMiddle_target_normalization]
  rw [Category.assoc, kummerCoefficient_single_resolution_homology]

end Stacks.EtaleCohomology
end
