/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerExtendedCoefficientNaturality
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomologyFactorsh

/-!
# Actual exact-derived homology comparison on the chosen homotopy resolution

Use the original mapDerivedCategoryHomologyIso_hom_app_Qh theorem,
not a replacement exact homology comparison. This cancels its inverse and factorsh;
matching the remaining ordinary/extended-homology tails is still required.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
attribute [local instance] HasDerivedCategory.standard

private lemma cancelComparisonTail {C : Type*} [Category C]
    {A B D E H : C} (e : A ≅ B) (k : B ≅ H)
    (d : A ⟶ D) (h : D ⟶ E) (c : E ⟶ H)
    (he : e.hom = d ≫ h ≫ c ≫ k.inv) :
    e.inv ≫ d ≫ h ≫ c = k.hom := by
  have hp := congrArg (fun f => e.inv ≫ f ≫ k.hom) he
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.comp_id] using hp.symm

namespace Stacks.EtaleCohomology
variable (Λ : Type) [CommRing Λ]

/-- The original inverse exact homology comparison cancels precisely the existing
factorsh and exact homotopy-homology comparison on any actual bounded-below object. -/
theorem kummerExactHomologyFactors_cancel
    (K : HomotopyCategory.Plus (ModuleCat.{u + 1} Λ)) (q : ℕ) :
    let R := ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)
    let J := (HomotopyCategory.Plus.ι (ModuleCat.{u + 1} Λ)).obj K
    (Stacks.ExactDerivedPlus.mapDerivedCategoryPlusHomologyIso R (q : ℤ)
      (DerivedCategory.Plus.Qh.obj K)).inv ≫
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ) (q : ℤ)).map
        (R.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
      (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{u + 1} ℤ) (q : ℤ)).hom.app
        ((R.mapHomotopyCategory (.up ℤ)).obj J) ≫
      (R.mapHomotopyCategoryHomologyIso (.up ℤ) (q : ℤ)).hom.app J =
    R.map ((DerivedCategory.homologyFunctorFactorsh (ModuleCat.{u + 1} Λ)
      (q : ℤ)).hom.app J) := by
  let R := ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)
  let J := (HomotopyCategory.Plus.ι (ModuleCat.{u + 1} Λ)).obj K
  exact cancelComparisonTail
    ((R.mapDerivedCategoryHomologyIso (q : ℤ)).app (DerivedCategory.Qh.obj J))
    (R.mapIso ((DerivedCategory.homologyFunctorFactorsh (ModuleCat.{u + 1} Λ)
      (q : ℤ)).app J)) _ _ _
    (R.mapDerivedCategoryHomologyIso_hom_app_Qh (q : ℤ) J)

/-- The same identity on the actual global-sections image of the original chosen resolution. -/
theorem kummerExactHomologyFactors_chosen
    (X : Scheme.{u}) (M : EtaleModules.{u, 0} Λ X) (q : ℕ) :
    let R := ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)
    let G := etaleModuleGlobalSections.{u, 0} Λ X
    let K := G.mapHomotopyCategoryPlus.obj (Stacks.DerivedIndexing.resPlus.obj M)
    let J := (HomotopyCategory.Plus.ι (ModuleCat.{u + 1} Λ)).obj K
    (Stacks.ExactDerivedPlus.mapDerivedCategoryPlusHomologyIso R (q : ℤ)
      (DerivedCategory.Plus.Qh.obj K)).inv ≫
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ) (q : ℤ)).map
        (R.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
      (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{u + 1} ℤ) (q : ℤ)).hom.app
        ((R.mapHomotopyCategory (.up ℤ)).obj J) ≫
      (R.mapHomotopyCategoryHomologyIso (.up ℤ) (q : ℤ)).hom.app J =
    R.map ((DerivedCategory.homologyFunctorFactorsh (ModuleCat.{u + 1} Λ)
      (q : ℤ)).hom.app J) := by
  exact kummerExactHomologyFactors_cancel Λ _ q

end Stacks.EtaleCohomology
end
