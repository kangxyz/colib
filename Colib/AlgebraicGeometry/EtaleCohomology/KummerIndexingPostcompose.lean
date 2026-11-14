/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerModuleComparisonNaturality
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedPostcomposeIndexing

/-!
# Original comparison indexing factors

Explicit factors of the original indexing maps, without replacing the comparison.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
attribute [local instance] HasDerivedCategory.standard
private lemma cancelIsoTail {A : Type*} [Category* A]
    {V₀ V₁ V₂ V₃ V₄ : A} {p : V₀ ⟶ V₁} {q : V₁ ⟶ V₂}
    (i : V₃ ≅ V₂) {z : V₀ ⟶ V₃} (r : V₂ ⟶ V₄)
    (h : p ≫ q ≫ i.inv = z) : p ≫ q ≫ r = z ≫ i.hom ≫ r := by
  rw [← h]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

namespace Stacks.EtaleCohomology

/-- The exact original indexing map, with its two definitional factors isolated. -/
theorem kummerIndexingForget_factors (Λ : Type) [CommRing Λ] (X : Scheme.{u})
    (M : EtaleModules.{u, 0} Λ X) (n : ℕ) :
    let G := etaleModuleGlobalSections.{u, 0} Λ X
    let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
    U.map ((Stacks.DerivedIndexing.rightDerivedIso G n).hom.app M) =
      U.map ((Stacks.DerivedIndexing.rightDerivedIsoRes G n).hom.app M) ≫
        U.map ((Stacks.DerivedIndexing.rightDerivedPlusIsoRes G (n : ℤ)).inv.app M) := by
  exact Functor.map_comp _ _ _

/-- Explicit postcomposition factors in the original indexing comparison. -/
theorem kummerIndexingPostcompose (Λ : Type) [CommRing Λ] (X : Scheme.{u})
    (M : EtaleModules.{u, 0} Λ X) (n : ℕ) :
    let G := etaleModuleGlobalSections.{u, 0} Λ X
    let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
    (Functor.rightDerivedCompIso G U n).hom.app M ≫
        U.map ((Stacks.DerivedIndexing.rightDerivedIso G n).hom.app M) =
      (Stacks.DerivedIndexing.rightDerivedIsoRes (G ⋙ U) n).hom.app M ≫
        (U.mapHomotopyCategoryHomologyIso (ComplexShape.up ℤ) (n : ℤ)).hom.app
          ((G.mapHomotopyCategory (ComplexShape.up ℤ)).obj
            (Stacks.DerivedIndexing.resH.obj M)) ≫
        U.map ((Stacks.DerivedIndexing.rightDerivedPlusIsoRes G (n : ℤ)).inv.app M) := by
  dsimp only
  let G := etaleModuleGlobalSections.{u, 0} Λ X
  let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  have h := Stacks.DerivedIndexing.rightDerivedCompIso_hom_app_comp_rightDerivedIsoRes
    G U n M
  have hf := congrArg (fun f => (Functor.rightDerivedCompIso G U n).hom.app M ≫ f)
    (kummerIndexingForget_factors Λ X M n)
  exact hf.trans (cancelIsoTail
    ((U.mapHomotopyCategoryHomologyIso (ComplexShape.up ℤ) (n : ℤ)).app
      ((G.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        (Stacks.DerivedIndexing.resH.obj M))) _ h)

end Stacks.EtaleCohomology
end
