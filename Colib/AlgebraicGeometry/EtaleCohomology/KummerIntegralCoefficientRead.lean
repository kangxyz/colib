/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerOriginalComparisonTail

/-!
# Reading the original integral coefficient comparison

Cancel the actual target comparison and retain every original source
indexing/derived-restriction factor. No equality to an alternate Ext map is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
open Stacks.Cohomology.ModuleComparison
universe u
attribute [local instance] HasDerivedCategory.standard
private lemma cancelIsoTriple {C : Type*} [Category C]
    {A B D E : C} (a : A ≅ B) (b : B ≅ D) (c : D ≅ E) :
    (a ≪≫ Iso.refl B ≪≫ b ≪≫ c).hom ≫ c.inv = a.hom ≫ b.hom := by
  simp

namespace Stacks.EtaleCohomology
variable (Λ : Type) [CommRing Λ] (X : Scheme.{u})

/-- Cancel the actual integral target comparison in the ORIGINAL coefficient map. -/
theorem kummerIntegralCoefficient_cancel_target (M : EtaleModules.{u, 0} Λ X) (q : ℕ) :
    (extConstantRestrictScalarsIso (Int.castRingHom Λ) X M q).hom ≫
      (etaleModuleRightDerivedPlusIsoExt ℤ X
        ((etaleModuleRestrictScalars (Int.castRingHom Λ) X).obj M) q).inv =
    (etaleModuleRightDerivedPlusIsoExt Λ X M q).inv ≫
      (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).map
        (rightDerivedPlusRestrictScalarsIso (Int.castRingHom Λ) X M q).hom := by
  exact cancelIsoTriple (etaleModuleRightDerivedPlusIsoExt Λ X M q).symm
    ((forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).mapIso
      (rightDerivedPlusRestrictScalarsIso (Int.castRingHom Λ) X M q))
    (etaleModuleRightDerivedPlusIsoExt ℤ X
      ((etaleModuleRestrictScalars (Int.castRingHom Λ) X).obj M) q)


end Stacks.EtaleCohomology
end
