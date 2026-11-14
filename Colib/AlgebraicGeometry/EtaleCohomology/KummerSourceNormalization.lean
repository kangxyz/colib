/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerCoefficientSingleResolution

/-!
# Original source indexing normalization and coefficient source-unit cancellation

All indexing and source units are the actual original definitions.
This does not assert equality of the final Ext comparisons.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.HigherDirectImagePresheaf
universe u
attribute [local instance] HasDerivedCategory.standard
private lemma stripIsoTail {C : Type*} [Category C] {A B D E : C}
    (a : A ⟶ B) (b : B ⟶ D) (i : E ≅ D) :
    (a ≫ b ≫ i.inv) ≫ i.hom = a ≫ b := by simp
namespace Stacks.EtaleCohomology
variable (Λ : Type) [CommRing Λ] (X : Scheme.{u})

/-- Original indexing followed by the actual ordinary resolution identification is
exactly the existing derived-resolution reading followed by extended homology. -/
theorem kummerSourceIndexing_normalization (M : EtaleModules.{u, 0} Λ X) (q : ℕ) :
    let G := etaleModuleGlobalSections.{u, 0} Λ X
    let I := injectiveResolution M
    (Stacks.DerivedIndexing.rightDerivedIso G q).inv.app M ≫
      (I.isoRightDerivedObj G q).hom =
    (derivedPlusResolutionHomologyIso G I q).hom ≫
      (extendedHomologyIso G I.cocomplex q).hom := by
  let G := etaleModuleGlobalSections.{u, 0} Λ X
  let I := injectiveResolution M
  have h := congrArg (fun f => f ≫ (I.isoRightDerivedObj G q).hom)
    (Stacks.DerivedIndexing.rightDerivedIso_inv_app_eq G q M)
  exact h.trans (stripIsoTail _ _ (I.isoRightDerivedObj G q))

/-- Coefficient source augmentation and inverse mapped source unit combine into the
exact image of the ORIGINAL source resolution-normalization morphism. -/
theorem kummerCoefficientSource_cancel_unit (M : EtaleModules.{u, 0} Λ X) :
    let G := etaleModuleGlobalSections.{u, 0} Λ X
    let R := ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)
    let K := Stacks.DerivedIndexing.resPlus.obj M
    let a := (Stacks.DerivedIndexing.singleIsoResPlusQh
      (C := EtaleModules.{u, 0} Λ X)).app M
    have := kummerGlobalSectionsUnit_isIso Λ X K (fun _ => inferInstance)
    kummerCoefficientSourceAugmentation Λ X M ≫
      (kummerCoefficientResolutionSourceIso Λ X M).inv =
    R.mapDerivedCategoryPlus.map
      (G.rightDerivedFunctorPlus.map a.hom ≫ inv (G.rightDerivedFunctorPlusUnith.app K)) := by
  let G := etaleModuleGlobalSections.{u, 0} Λ X
  let R := ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)
  let K := Stacks.DerivedIndexing.resPlus.obj M
  have := kummerGlobalSectionsUnit_isIso Λ X K (fun _ => inferInstance)
  change R.mapDerivedCategoryPlus.map
      (G.rightDerivedFunctorPlus.map ((Stacks.DerivedIndexing.singleIsoResPlusQh
        (C := EtaleModules.{u, 0} Λ X)).app M).hom) ≫
      inv (R.mapDerivedCategoryPlus.map (G.rightDerivedFunctorPlusUnith.app K)) = _
  rw [← Functor.map_inv, ← Functor.map_comp]

/-- The original source normalization uses precisely the original augmentation
and inverse actual unit appearing in coefficient source cancellation. -/
theorem kummerSourceNormalization_factors (M : EtaleModules.{u, 0} Λ X) (q : ℕ) :
    let G := etaleModuleGlobalSections.{u, 0} Λ X
    let K := Stacks.DerivedIndexing.resPlus.obj M
    let a := (Stacks.DerivedIndexing.singleIsoResPlusQh
      (C := EtaleModules.{u, 0} Λ X)).app M
    have := kummerGlobalSectionsUnit_isIso Λ X K (fun _ => inferInstance)
    (derivedPlusResolutionHomologyIso G (injectiveResolution M) q).hom =
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) (q : ℤ)).map
      (G.rightDerivedFunctorPlus.map a.hom ≫ inv (G.rightDerivedFunctorPlusUnith.app K)) := by
  have ha : resolutionDerivedIso (injectiveResolution M) =
      (Stacks.DerivedIndexing.singleIsoResPlusQh
        (C := EtaleModules.{u, 0} Λ X)).app M :=
    Iso.ext (Stacks.DerivedIndexing.resolutionDerivedIso_hom_eq M)
  dsimp only [derivedPlusResolutionHomologyIso, Functor.mapIso_hom,
    Iso.trans_hom, Iso.symm_hom, asIso_inv]
  rw [ha]
  rfl

end Stacks.EtaleCohomology
end
