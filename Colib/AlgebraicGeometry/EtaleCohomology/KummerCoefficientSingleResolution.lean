/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerNamedSingleComparison

/-!
# Original single-object coefficient comparison on actual resolution homology

Paste the proved original coefficient augmentation and the proved named
target augmentation before applying homology. No Ext equivalence equality is assumed.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.HigherDirectImagePresheaf
universe u
attribute [local instance] HasDerivedCategory.standard

private lemma pasteAugmentations {C : Type*} [Category C]
    {A B D E F G H I : C}
    {x : A ⟶ D} {f : A ⟶ B} {y : B ⟶ E} {g : E ⟶ D}
    {s : D ⟶ F} {b : F ⟶ G} {h : E ⟶ H} {p : H ⟶ G} {u : G ⟶ I}
    (hx : x = f ≫ y ≫ g) (ht : g ≫ s ≫ b = h ≫ p) :
    x ≫ s ≫ b ≫ u = f ≫ (y ≫ h ≫ p ≫ u) := by
  rw [hx]
  simpa only [Category.assoc] using congrArg (fun k => f ≫ y ≫ k ≫ u) ht

private lemma mapResolutionPaste {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B E : C} {x : A ⟶ E} {f : A ⟶ B} {y : B ⟶ E}
    {V W : D} {e : F.obj E ⟶ W} {r : F.obj B ⟶ V} {s : V ⟶ W}
    (hx : x = f ≫ y) (hy : F.map y ≫ e = r ≫ s) :
    F.map x ≫ e = F.map f ≫ r ≫ s := by
  rw [hx, Functor.map_comp, Category.assoc, hy]

namespace Stacks.EtaleCohomology
variable (Λ : Type) [CommRing Λ] (X : Scheme.{u})

/-- Original coefficient map at the single object followed by the ACTUAL named
exact-single iso, target indexing augmentation, and inverse target resolution unit. -/
def kummerCoefficientSingleResolutionLeft (M : EtaleModules.{u, 0} Λ X) :=
  let T := etaleModuleRestrictScalars (Int.castRingHom Λ) X
  let H := etaleModuleDerivedGlobalSections.{u, 0} ℤ X
  let b := (Stacks.DerivedIndexing.singleIsoResPlusQh
    (C := EtaleModules.{u, 0} ℤ X)).app (T.obj M)
  (etaleModuleDerivedGlobalSectionsRestrictScalars (Int.castRingHom Λ) X).hom.app
      ((DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} Λ X) 0).obj M) ≫
    H.map (T.mapDerivedCategoryPlusObjSingleIso M).hom ≫ H.map b.hom ≫
    (kummerRestrictedTargetUnitIso Λ X M).inv

/-- Actual source augmentation in the source of the original coefficient iso. -/
def kummerCoefficientSourceAugmentation (M : EtaleModules.{u, 0} Λ X) :=
  ((etaleModuleDerivedGlobalSections.{u, 0} Λ X) ⋙
    (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)).mapDerivedCategoryPlus).map
    ((Stacks.DerivedIndexing.singleIsoResPlusQh
      (C := EtaleModules.{u, 0} Λ X)).app M).hom

/-- Paste both ORIGINAL augmentations and the actual chosen comparison. -/
theorem kummerCoefficient_single_resolution (M : EtaleModules.{u, 0} Λ X) :
    kummerCoefficientSingleResolutionLeft Λ X M =
      kummerCoefficientSourceAugmentation Λ X M ≫
        kummerCoefficientResolutionLeft Λ X M := by
  let H := etaleModuleDerivedGlobalSections.{u, 0} ℤ X
  have ht := congrArg H.map (kummerTargetAugmentation_named Λ X M)
  simp only [Functor.map_comp] at ht
  have hf := H.map_comp
    ((etaleModuleRestrictScalars (Int.castRingHom Λ) X).mapDerivedCategoryPlusFactorsh.hom.app
      (Stacks.DerivedIndexing.resPlus.obj M))
    (DerivedCategory.Plus.Qh.map (kummerRestrictedResolutionPlus Λ X M))
  exact pasteAugmentations
    (kummerOriginalDerivedCoefficient_single_resolution Λ X M) (ht.trans hf)

/-- The original single-object coefficient map, transported by actual target maps,
acts on homology by the actual chosen resolution map with original source factors. -/
theorem kummerCoefficient_single_resolution_homology
    (M : EtaleModules.{u, 0} Λ X) (q : ℕ) :
    let T := etaleModuleRestrictScalars (Int.castRingHom Λ) X
    let H := etaleModuleGlobalSections.{u, 0} ℤ X
    let D := DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ) (q : ℤ)
    D.map (kummerCoefficientSingleResolutionLeft Λ X M) ≫
      (extendedHomologyIso H (injectiveResolution (T.obj M)).cocomplex q).hom =
    D.map (kummerCoefficientSourceAugmentation Λ X M) ≫
      D.map (kummerCoefficientResolutionPrefix Λ X M) ≫
      (extendedHomologyIso (T ⋙ H) (injectiveResolution M).cocomplex q).hom ≫
      HomologicalComplex.homologyMap
        ((H.mapHomologicalComplex (ComplexShape.up ℕ)).map
          (kummerRestrictedResolutionComparison Λ X M)) q := by
  exact mapResolutionPaste
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ) (q : ℤ))
    (kummerCoefficient_single_resolution Λ X M)
    (kummerCoefficientResolution_homology Λ X M q)

end Stacks.EtaleCohomology
end
