/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerHomotopyOrdinaryTail

/-! # Original exact-derived comparison and the actual extended global-sections tail -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open Stacks.Cohomology.HigherDirectImagePresheaf Stacks.DerivedIndexing
universe u
attribute [local instance] HasDerivedCategory.standard

private lemma pasteTail {C : Type*} [Category C]
    {A B D E F H I : C} (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) (d : E ⟶ F)
    (e : A ⟶ F) (f : F ⟶ I) (g : E ⟶ H) (h : H ⟶ I)
    (h₁ : a ≫ b ≫ c ≫ d = e) (h₂ : d ≫ f = g ≫ h) :
    a ≫ b ≫ (c ≫ g) ≫ h = e ≫ f := by
  rw [← h₁]
  simpa only [Category.assoc] using congrArg (fun z => a ≫ b ≫ c ≫ z) h₂.symm

private lemma changeMiddle {C : Type*} [Category C]
    {A B D E F : C} (a : A ⟶ B) (b : B ⟶ D) (t u : D ⟶ E)
    (h : E ⟶ F) (r : A ⟶ F) (ht : t = u) (he : a ≫ b ≫ u ≫ h = r) :
    a ≫ b ≫ t ≫ h = r := by
  rw [ht]
  exact he

namespace Stacks.EtaleCohomology
variable (Λ : Type) [CommRing Λ] (X : Scheme.{u})

set_option backward.isDefEq.respectTransparency false in
/-- The ORIGINAL exact-derived homology comparison and its factorsh send the original
extended Γ-then-restriction tail to the exact image of the original extended Γ-tail.
This does not identify the final Ext equivalence. -/
theorem kummerExactExtendedTail (M : EtaleModules.{u, 0} Λ X) (q : ℕ) :
    let G := etaleModuleGlobalSections.{u, 0} Λ X
    let R := ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)
    let K := (injectiveResolution M).cocomplex
    let L := G.mapHomotopyCategoryPlus.obj (Stacks.DerivedIndexing.resPlus.obj M)
    (Stacks.ExactDerivedPlus.mapDerivedCategoryPlusHomologyIso R (q : ℤ)
      (DerivedCategory.Plus.Qh.obj L)).inv ≫
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ) (q : ℤ)).map
        (R.mapDerivedCategoryPlusFactorsh.hom.app L) ≫
      (extendedHomologyIso (G ⋙ R) K q).hom ≫
      (mapExactHomologyIso R ((G.mapHomologicalComplex (.up ℕ)).obj K) q).hom =
    R.map (extendedHomologyIso G K q).hom := by
  let G := etaleModuleGlobalSections.{u, 0} Λ X
  let R := ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)
  let K := (injectiveResolution M).cocomplex
  have h := pasteTail _ _ _ _ _ _ _ _
    (kummerExactHomologyFactors_chosen Λ X M q)
    (kummerHomotopyOrdinaryTail Λ X M q)
  have hs := kummerExtendedHomology_factors G K q
  have ht := kummerExtendedHomology_factors (G ⋙ R) K q
  have hr := congrArg R.map hs
  rw [R.map_comp] at hr
  have hresult := h.trans hr.symm
  exact changeMiddle _ _ _ _ _ _ ht hresult

end Stacks.EtaleCohomology
end
