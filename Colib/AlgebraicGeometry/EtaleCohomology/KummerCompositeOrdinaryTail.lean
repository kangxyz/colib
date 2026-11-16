/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerExactOrdinaryTail

/-!
# Composite global sections and exact coefficient ordinary tails

This keeps original mapExactHomologyIso and extendedHomologyTailIso.
Homotopy-to-complex factors and the final original Ext equality are not asserted.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open Stacks.Cohomology.HigherDirectImagePresheaf
open Stacks.Cohomology.ModulePushforwardComparison Stacks.DerivedIndexing
universe u
attribute [local instance] HasDerivedCategory.standard
namespace Stacks.EtaleCohomology
variable (Λ : Type) [CommRing Λ]

/-- Naturality of the actual short-complex exact-homology comparison on cochain maps. -/
theorem kummerExactHomology_naturality {K L : CochainComplex (ModuleCat.{u + 1} Λ) ℤ}
    (φ : K ⟶ L) (q : ℤ) :
    let R := ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)
    homologyMap ((R.mapHomologicalComplex (.up ℤ)).map φ) q ≫
      (mapExactHomologyIso R L q).hom =
    (mapExactHomologyIso R K q).hom ≫ R.map (homologyMap φ q) := by
  exact ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u + 1} Λ) (.up ℤ) q).map φ)
    (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ))

/-- Exact coefficients commute with the original ordinary tail of global sections
composed with coefficient restriction, not merely with extension alone. -/
theorem kummerCompositeOrdinaryTail
    (X : Scheme.{u}) (M : EtaleModules.{u, 0} Λ X) (q : ℕ) :
    let G := etaleModuleGlobalSections.{u, 0} Λ X
    let R := ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)
    let K := (injectiveResolution M).cocomplex
    (extendedHomologyTailIso (G ⋙ R) K q).hom ≫
      (mapExactHomologyIso R ((G.mapHomologicalComplex (.up ℕ)).obj K) q).hom =
    (mapExactHomologyIso R
      ((G.mapHomologicalComplex (.up ℤ)).obj (K.extend ComplexShape.embeddingUpNat))
      (q : ℤ)).hom ≫ R.map (extendedHomologyTailIso G K q).hom := by
  dsimp only
  rw [extendedHomologyTailIso_comp, Category.assoc, ← kummerExactOrdinaryTail]
  rw [← Category.assoc, kummerExactHomology_naturality, Category.assoc]
  rw [← Functor.map_comp]
  rfl

end Stacks.EtaleCohomology
end
