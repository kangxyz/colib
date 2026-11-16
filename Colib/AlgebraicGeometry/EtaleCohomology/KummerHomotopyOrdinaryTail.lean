/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerCompositeOrdinaryTail

/-!
# Actual homotopy-to-complex factors and ordinary coefficient tails

Match the original homotopy homology comparison with the already verified
ordinary tail formula. The final derived source arrow and Ext equivalence still require assembly.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open Stacks.Cohomology.HigherDirectImagePresheaf Stacks.DerivedIndexing
universe u
attribute [local instance] HasDerivedCategory.standard

private lemma cancelMappedTail {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B : C} (e : A ≅ B) {X Y : D} (a : X ⟶ Y) (b : Y ⟶ F.obj B) :
    (a ≫ b ≫ F.map e.inv) ≫ F.map e.hom = a ≫ b := by
  simp only [Category.assoc, ← F.map_comp, e.inv_hom_id, F.map_id, Category.comp_id]

namespace Stacks.EtaleCohomology
variable (Λ : Type) [CommRing Λ]

set_option backward.isDefEq.respectTransparency false in
/-- On an actual complex, the original homotopy exact-homology comparison followed
by the original homotopy-to-complex factor is the ordinary exact comparison. -/
theorem kummerHomotopyExactHomology_factors
    (Z : CochainComplex (ModuleCat.{u + 1} Λ) ℤ) (q : ℤ) :
    let R := ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)
    (R.mapHomotopyCategoryHomologyIso (.up ℤ) q).hom.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj Z) ≫
      R.map ((HomotopyCategory.homologyFunctorFactors (ModuleCat.{u + 1} Λ)
        (.up ℤ) q).hom.app Z) =
    (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u + 1} ℤ) (.up ℤ) q).hom.app
      ((R.mapHomologicalComplex (.up ℤ)).obj Z) ≫
      (mapExactHomologyIso R Z q).hom := by
  dsimp only
  rw [mapHomotopyCategoryHomologyIso_hom_app_quotient]
  exact cancelMappedTail
    (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ))
    ((HomotopyCategory.homologyFunctorFactors (ModuleCat.{u + 1} Λ) (.up ℤ) q).app Z) _ _



set_option backward.isDefEq.respectTransparency false in
/-- The original homotopy exact-homology comparison carries the whole actual Γ-tail
to the actual Γ-then-restriction tail and ordinary exact homology comparison. -/
theorem kummerHomotopyOrdinaryTail
    (X : Scheme.{u}) (M : EtaleModules.{u, 0} Λ X) (q : ℕ) :
    let G := etaleModuleGlobalSections.{u, 0} Λ X
    let R := ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)
    let K := (injectiveResolution M).cocomplex
    let Z := (G.mapHomologicalComplex (.up ℤ)).obj (K.extend ComplexShape.embeddingUpNat)
    (R.mapHomotopyCategoryHomologyIso (.up ℤ) (q : ℤ)).hom.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj Z) ≫
      R.map (kummerOrdinaryExtendedTail G K q) =
    kummerOrdinaryExtendedTail (G ⋙ R) K q ≫
      (mapExactHomologyIso R ((G.mapHomologicalComplex (.up ℕ)).obj K) q).hom := by
  dsimp only
  simp only [kummerOrdinaryExtendedTail, homologyFunctorObjIso, Iso.refl_hom,
    Category.id_comp, Functor.map_comp]
  rw [← Category.assoc, kummerHomotopyExactHomology_factors, Category.assoc,
    ← kummerCompositeOrdinaryTail, ← Category.assoc]
  rfl

end Stacks.EtaleCohomology
end
