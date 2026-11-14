/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerSourceNormalization

/-!
# Exact coefficient homology and the original source normalizer

Use naturality of the EXISTING exact-derived homology iso. This is not a
new substitute comparison; its specialization cancels the actual source-unit factors.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.HigherDirectImagePresheaf
universe u
attribute [local instance] HasDerivedCategory.standard
namespace Stacks.EtaleCohomology
variable (Λ : Type) [CommRing Λ]

/-- Naturality of the actual exact coefficient homology comparison used in the
original rightDerivedPlusRestrictScalarsIso. -/
theorem kummerExactCoefficientHomology_naturality
    {K L : DerivedCategory.Plus (ModuleCat.{u + 1} Λ)} (f : K ⟶ L) (q : ℕ) :
    let R := ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)
    (Stacks.ExactDerivedPlus.mapDerivedCategoryPlusHomologyIso R (q : ℤ) K).inv ≫
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ) (q : ℤ)).map
        (R.mapDerivedCategoryPlus.map f) =
    R.map ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) (q : ℤ)).map f) ≫
      (Stacks.ExactDerivedPlus.mapDerivedCategoryPlusHomologyIso R (q : ℤ) L).inv := by
  let R := ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)
  exact ((R.mapDerivedCategoryHomologyIso (q : ℤ)).inv.naturality
    (DerivedCategory.Plus.ι.map f)).symm

variable (X : Scheme.{u})
/-- Actual original source augmentation followed by inverse actual source unit. -/
def kummerSourceNormalizerArrow (M : EtaleModules.{u, 0} Λ X) :=
  let G := etaleModuleGlobalSections.{u, 0} Λ X
  let K := Stacks.DerivedIndexing.resPlus.obj M
  have := kummerGlobalSectionsUnit_isIso Λ X K (fun _ => inferInstance)
  G.rightDerivedFunctorPlus.map
      ((Stacks.DerivedIndexing.singleIsoResPlusQh
        (C := EtaleModules.{u, 0} Λ X)).app M).hom ≫
    inv (G.rightDerivedFunctorPlusUnith.app K)

/-- Original exact coefficient homology factor sends source augmentation/unit
normalization to the exact image of the ORIGINAL source resolution homology reading. -/
theorem kummerExactCoefficientHomology_source_normalization
    (M : EtaleModules.{u, 0} Λ X) (q : ℕ) :
    let G := etaleModuleGlobalSections.{u, 0} Λ X
    let R := ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)
    let K := Stacks.DerivedIndexing.resPlus.obj M
    let A := G.rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} Λ X) 0).obj M)
    let B := DerivedCategory.Plus.Qh.obj (G.mapHomotopyCategoryPlus.obj K)
    (Stacks.ExactDerivedPlus.mapDerivedCategoryPlusHomologyIso R (q : ℤ) A).inv ≫
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ) (q : ℤ)).map
        (kummerCoefficientSourceAugmentation Λ X M ≫
          (kummerCoefficientResolutionSourceIso Λ X M).inv) =
    R.map (derivedPlusResolutionHomologyIso G (injectiveResolution M) q).hom ≫
      (Stacks.ExactDerivedPlus.mapDerivedCategoryPlusHomologyIso R (q : ℤ) B).inv := by
  let G := etaleModuleGlobalSections.{u, 0} Λ X
  let R := ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)
  let D := DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ) (q : ℤ)
  let A := G.rightDerivedFunctorPlus.obj
    ((DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} Λ X) 0).obj M)
  let B := DerivedCategory.Plus.Qh.obj
    (G.mapHomotopyCategoryPlus.obj (Stacks.DerivedIndexing.resPlus.obj M))
  have hsource := congrArg (fun f =>
    (Stacks.ExactDerivedPlus.mapDerivedCategoryPlusHomologyIso R (q : ℤ) A).inv ≫ D.map f)
    (kummerCoefficientSource_cancel_unit Λ X M)
  have hn := kummerExactCoefficientHomology_naturality Λ (kummerSourceNormalizerArrow Λ X M) q
  have hreading := congrArg (fun f => R.map f ≫
    (Stacks.ExactDerivedPlus.mapDerivedCategoryPlusHomologyIso R (q : ℤ) B).inv)
    (kummerSourceNormalization_factors Λ X M q).symm
  exact hsource.trans (hn.trans hreading)

end Stacks.EtaleCohomology
end
