/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerIntegralCocycleRead

/-!
# The original derived coefficient comparison along its original resolution augmentation

Use the actual original singleIsoResPlusQh and naturality of the actual
original derived coefficient isomorphism. No alternate comparison is introduced.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
attribute [local instance] HasDerivedCategory.standard

private lemma natTransAtIso {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (a : F ⟶ G) {A B : C} (i : A ≅ B) :
    a.app A = F.map i.hom ≫ a.app B ≫ G.map i.inv := by
  rw [← Category.assoc, a.naturality]
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id]
  rw [G.map_id, Category.comp_id]

namespace Stacks.EtaleCohomology
variable (Λ : Type) [CommRing Λ] (X : Scheme.{u})

/-- The ORIGINAL comparison at the single object is its component on the ORIGINAL
chosen resolution, conjugated by its actual augmentation isomorphism. -/
theorem kummerOriginalDerivedCoefficient_single_resolution
    (M : EtaleModules.{u, 0} Λ X) :
    let R := ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)
    let T := etaleModuleRestrictScalars (Int.castRingHom Λ) X
    let G := etaleModuleDerivedGlobalSections.{u, 0} Λ X
    let H := etaleModuleDerivedGlobalSections.{u, 0} ℤ X
    let a := (Stacks.DerivedIndexing.singleIsoResPlusQh (C := EtaleModules.{u, 0} Λ X)).app M
    (etaleModuleDerivedGlobalSectionsRestrictScalars (Int.castRingHom Λ) X).hom.app
      ((DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} Λ X) 0).obj M) =
      (G ⋙ R.mapDerivedCategoryPlus).map a.hom ≫
      (etaleModuleDerivedGlobalSectionsRestrictScalars (Int.castRingHom Λ) X).hom.app
        (DerivedCategory.Plus.Qh.obj (Stacks.DerivedIndexing.resPlus.obj M)) ≫
      (T.mapDerivedCategoryPlus ⋙ H).map a.inv := by
  exact natTransAtIso
    (etaleModuleDerivedGlobalSectionsRestrictScalars (Int.castRingHom Λ) X).hom
    ((Stacks.DerivedIndexing.singleIsoResPlusQh (C := EtaleModules.{u, 0} Λ X)).app M)

/-- Homology of the same genuine augmentation transport, retaining the actual maps. -/
theorem kummerOriginalDerivedCoefficient_single_resolution_homology
    (M : EtaleModules.{u, 0} Λ X) (q : ℕ) :
    let R := ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)
    let T := etaleModuleRestrictScalars (Int.castRingHom Λ) X
    let G := etaleModuleDerivedGlobalSections.{u, 0} Λ X
    let H := etaleModuleDerivedGlobalSections.{u, 0} ℤ X
    let D := DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ) (q : ℤ)
    let a := (Stacks.DerivedIndexing.singleIsoResPlusQh (C := EtaleModules.{u, 0} Λ X)).app M
    D.map ((etaleModuleDerivedGlobalSectionsRestrictScalars (Int.castRingHom Λ) X).hom.app
      ((DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} Λ X) 0).obj M)) =
    D.map ((G ⋙ R.mapDerivedCategoryPlus).map a.hom) ≫
      D.map ((etaleModuleDerivedGlobalSectionsRestrictScalars (Int.castRingHom Λ) X).hom.app
        (DerivedCategory.Plus.Qh.obj (Stacks.DerivedIndexing.resPlus.obj M))) ≫
      D.map ((T.mapDerivedCategoryPlus ⋙ H).map a.inv) := by
  have h := congrArg
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ) (q : ℤ)).map
    (kummerOriginalDerivedCoefficient_single_resolution Λ X M)
  simpa only [Functor.map_comp] using h

end Stacks.EtaleCohomology
end
