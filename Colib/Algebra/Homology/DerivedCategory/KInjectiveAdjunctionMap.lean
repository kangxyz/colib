/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Homology.DerivedCategory.KInjectiveAdjunction
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Identifying the K-injective adjunction with exact inverse image and counit -/

/-!
Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Aglib/Algebra/Homology/DerivedCategory/KInjectiveAdjunctionMap.lean`, blob `c8d7ec9166eb16a2763882643cad5d4aace40ef6`.
The canonical native objects and displayed maps are retained. Source candidate only.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
universe w₁ w₂ v₁ v₂ u₁ u₂
namespace CategoryTheory.Adjunction
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Abelian C] [Abelian D] [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
  {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L] (adj : L ⊣ R)
  (K : CochainComplex C ℤ) (J : CochainComplex D ℤ)
  [J.IsKInjective] [CochainComplex.IsKInjective ((R.mapHomologicalComplex (.up ℤ)).obj J)]

/-- The constructed equivalence is the actual exact-functor map followed by the actual counit. -/
theorem kInjectiveHomAddEquiv_eq
    (x : DerivedCategory.Q.obj K ⟶
      DerivedCategory.Q.obj ((R.mapHomologicalComplex (.up ℤ)).obj J)) :
    adj.kInjectiveHomAddEquiv K J x =
      L.mapDerivedCategoryFactors.inv.app K ≫ L.mapDerivedCategory.map x ≫
        L.mapDerivedCategoryFactors.hom.app _ ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex adj.counit (.up ℤ)).app J) := by
  obtain ⟨f, rfl⟩ := CochainComplex.IsKInjective.Q_map_surjective K _ x
  rw [adj.kInjectiveHomAddEquiv_map, L.mapDerivedCategoryFactors_hom_naturality_assoc]
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp, Functor.map_comp]

/-- No derived adjunction comparison is assumed: the specified original map is bijective. -/
theorem kInjectiveHomMap_bijective :
    Function.Bijective (fun x : DerivedCategory.Q.obj K ⟶
        DerivedCategory.Q.obj ((R.mapHomologicalComplex (.up ℤ)).obj J) =>
      L.mapDerivedCategoryFactors.inv.app K ≫ L.mapDerivedCategory.map x ≫
        L.mapDerivedCategoryFactors.hom.app _ ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex adj.counit (.up ℤ)).app J)) := by
  simpa only [← adj.kInjectiveHomAddEquiv_eq] using (adj.kInjectiveHomAddEquiv K J).bijective

end CategoryTheory.Adjunction
