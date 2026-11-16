/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerTermwiseArrowRead

/-!
# Actual coefficient termwise arrow and extended homology

Paste the original bounded-arrow reading, original extended naturality,
and original exact-derived/extended-tail coherence. Final Ext equality remains unproved.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open Stacks.Cohomology.HigherDirectImagePresheaf Stacks.DerivedIndexing
universe u
attribute [local instance] HasDerivedCategory.standard

private lemma pasteExactTail {C : Type*} [Category C]
    {A B D E H I J : C} (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E)
    (d : E ⟶ H) (e : D ⟶ I) (f : I ⟶ H) (s : I ≅ J) (r : A ⟶ J)
    (hn : c ≫ d = e ≫ f) (he : a ≫ b ≫ e ≫ s.hom = r) :
    a ≫ b ≫ c ≫ d = r ≫ s.inv ≫ f := by
  rw [hn, ← he]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

private lemma pasteThree {C : Type*} [Category C]
    {A B D E F G H I J K : C} (m : A ⟶ G)
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) (d : E ⟶ F) (f : F ⟶ G)
    (r : A ⟶ H) (s : H ⟶ I) (t : I ⟶ E)
    (x : H ⟶ J) (y : J ⟶ K) (z : K ⟶ F)
    (h₁ : m = a ≫ b ≫ c ≫ d ≫ f)
    (h₂ : a ≫ b ≫ c = r ≫ s ≫ t)
    (h₃ : s ≫ t ≫ d = x ≫ y ≫ z) :
    m = r ≫ x ≫ y ≫ z ≫ f := by
  have hp := congrArg (fun v => v ≫ d ≫ f) h₂
  simp only [Category.assoc] at hp
  rw [h₁, hp]
  simpa only [Category.assoc] using congrArg (fun v => r ≫ v ≫ f) h₃

namespace Stacks.EtaleCohomology
variable (Λ : Type) [CommRing Λ] (X : Scheme.{u})

/-- The ORIGINAL bounded coefficient arrow acts on original extended homology by
the actual original coefficient natural transformation on the chosen complex. -/
theorem kummerBoundedArrow_extendedHomology
    (M : EtaleModules.{u, 0} Λ X) (q : ℕ) :
    let G := etaleModuleGlobalSections.{u, 0} Λ X
    let R := ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)
    let T := etaleModuleRestrictScalars (Int.castRingHom Λ) X
    let H := etaleModuleGlobalSections.{u, 0} ℤ X
    let K := (injectiveResolution M).cocomplex
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ) (q : ℤ)).map
      (DerivedCategory.Plus.Qh.map (kummerCoefficientBoundedArrow Λ X M)) ≫
      (extendedHomologyIso (T ⋙ H) K q).hom =
    (extendedHomologyIso (G ⋙ R) K q).hom ≫
      homologyMap
        (((etaleModuleGlobalSectionsRestrictScalars (Int.castRingHom Λ) X).hom.mapHomologicalComplex
          (.up ℕ)).app K) q := by
  exact kummerOriginalCoefficient_extendedHomology Λ X M q

/-- The full ORIGINAL termwise arrow, including its actual exact-derived factorsh,
now has its actual extended-homology formula. No Ext equivalence is substituted. -/
theorem kummerTermwiseArrow_extendedHomology
    (M : EtaleModules.{u, 0} Λ X) (q : ℕ) :
    let G := etaleModuleGlobalSections.{u, 0} Λ X
    let R := ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)
    let T := etaleModuleRestrictScalars (Int.castRingHom Λ) X
    let H := etaleModuleGlobalSections.{u, 0} ℤ X
    let K := (injectiveResolution M).cocomplex
    let L := G.mapHomotopyCategoryPlus.obj (Stacks.DerivedIndexing.resPlus.obj M)
    (Stacks.ExactDerivedPlus.mapDerivedCategoryPlusHomologyIso R (q : ℤ)
      (DerivedCategory.Plus.Qh.obj L)).inv ≫
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ) (q : ℤ)).map
        (kummerCoefficientTermwiseArrow Λ X M) ≫
      (extendedHomologyIso (T ⋙ H) K q).hom =
    R.map (extendedHomologyIso G K q).hom ≫
      (mapExactHomologyIso R ((G.mapHomologicalComplex (.up ℕ)).obj K) q).inv ≫
      homologyMap
        (((etaleModuleGlobalSectionsRestrictScalars (Int.castRingHom Λ) X).hom.mapHomologicalComplex
          (.up ℕ)).app K) q := by
  have h := pasteExactTail _ _ _ _ _ _ _ _
    (kummerBoundedArrow_extendedHomology Λ X M q)
    (kummerExactExtendedTail Λ X M q)
  dsimp only
  rw [show kummerCoefficientTermwiseArrow Λ X M =
    (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)).mapDerivedCategoryPlusFactorsh.hom.app
      ((etaleModuleGlobalSections.{u, 0} Λ X).mapHomotopyCategoryPlus.obj
        (Stacks.DerivedIndexing.resPlus.obj M)) ≫
    DerivedCategory.Plus.Qh.map (kummerCoefficientBoundedArrow Λ X M) from rfl]
  rw [Functor.map_comp]
  exact (congrArg (fun z => _ ≫ z) (Category.assoc _ _ _)).trans h

set_option backward.isDefEq.respectTransparency false in
/-- The original coefficient comparison, in the actual chosen resolution models,
is the coefficient homology map followed by the actual resolution comparison. -/
theorem kummerOriginalMiddle_ordinaryHomology
    (M : EtaleModules.{u, 0} Λ X) (q : ℕ) :
    let T := etaleModuleRestrictScalars (Int.castRingHom Λ) X
    let G := etaleModuleGlobalSections.{u, 0} Λ X
    let H := etaleModuleGlobalSections.{u, 0} ℤ X
    let R := ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)
    let I := injectiveResolution M
    let J := injectiveResolution (T.obj M)
    (rightDerivedPlusRestrictScalarsIso (Int.castRingHom Λ) X M q).hom ≫
      (derivedPlusResolutionHomologyIso H J q).hom ≫
      (extendedHomologyIso H J.cocomplex q).hom =
    R.map ((derivedPlusResolutionHomologyIso G I q).hom ≫
      (extendedHomologyIso G I.cocomplex q).hom) ≫
      (mapExactHomologyIso R ((G.mapHomologicalComplex (.up ℕ)).obj I.cocomplex) q).inv ≫
      homologyMap
        (((etaleModuleGlobalSectionsRestrictScalars (Int.castRingHom Λ) X).hom.mapHomologicalComplex
          (.up ℕ)).app I.cocomplex) q ≫
      homologyMap ((H.mapHomologicalComplex (.up ℕ)).map
        (kummerRestrictedResolutionComparison Λ X M)) q := by
  have h := pasteThree _ _ _ _ _ _ _ _ _ _ _ _
    (kummerOriginalMiddle_resolution_homology Λ X M q)
    (kummerCoefficientPrefix_source_normalization Λ X M q)
    (kummerTermwiseArrow_extendedHomology Λ X M q)
  simpa only [Functor.map_comp, Category.assoc] using h

end Stacks.EtaleCohomology
end
