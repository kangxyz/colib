/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Realization.DoubleCylinder
public import Mathlib.CategoryTheory.Limits.Types.Pushouts
public import Mathlib.CategoryTheory.Limits.Types.Coproducts

/-!
# Simplex coverage of the actual double cylinder

Evaluation preserves the defining simplicial pushout. Every characteristic simplex
therefore factors through its cylinder or one of its original endpoint summands.
No topological quotient-product comparison is asserted here.

Adapted from `Quillen/Topology/Realization/DoubleCylinderSimplexCoverage.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits MonoidalCategory Opposite
open scoped Simplicial
universe u

namespace TopCat.DoubleCylinder

private theorem coprod_simplex_eq_or (Y Z : SSet.{u}) (n : SimplexCategoryᵒᵖ)
    (x : (Y ⨿ Z).obj n) :
    (∃ y, (coprod.inl : Y ⟶ Y ⨿ Z).app n y = x) ∨
      ∃ z, (coprod.inr : Z ⟶ Y ⨿ Z).app n z = x := by
  obtain ⟨⟨j⟩, y, hy⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves ((evaluation _ _).obj n) (coprodIsCoprod Y Z)) x
  cases j with
  | left => exact Or.inl ⟨y, hy⟩
  | right => exact Or.inr ⟨y, hy⟩

/-- Every simplex belongs to the actual cylinder or one of its two endpoint summands. -/
theorem simplex_eq_cylinder_or_left_or_right {X Y Z : SSet.{u}}
    (f : X ⟶ Y) (g : X ⟶ Z) (n : SimplexCategoryᵒᵖ)
    (x : (simplicial f g).obj n) :
    (∃ c, (simplicialCylinder f g).app n c = x) ∨
      (∃ y, ((coprod.inl : Y ⟶ Y ⨿ Z) ≫ simplicialEnds f g).app n y = x) ∨
        ∃ z, ((coprod.inr : Z ⟶ Y ⨿ Z) ≫ simplicialEnds f g).app n z = x := by
  obtain hc | ⟨e, he⟩ := Types.eq_or_eq_of_isPushout
    ((simplicial_isPushout f g).map ((evaluation _ _).obj n)) x
  · exact Or.inl hc
  · obtain ⟨y, hy⟩ | ⟨z, hz⟩ := coprod_simplex_eq_or Y Z n e
    · exact Or.inr (Or.inl ⟨y, by
        change (simplicialEnds f g).app n ((coprod.inl : Y ⟶ Y ⨿ Z).app n y) = x
        rw [hy]
        exact he⟩)
    · exact Or.inr (Or.inr ⟨z, by
        change (simplicialEnds f g).app n ((coprod.inr : Z ⟶ Y ⨿ Z).app n z) = x
        rw [hz]
        exact he⟩)

/-- A whole characteristic simplex factors through one original summand. -/
theorem characteristicSimplex_factors {X Y Z : SSet.{u}}
    (f : X ⟶ Y) (g : X ⟶ Z) (n : SimplexCategory)
    (σ : SSet.stdSimplex.obj n ⟶ simplicial f g) :
    (∃ c : SSet.stdSimplex.obj n ⟶ X ⊗ Δ[1], c ≫ simplicialCylinder f g = σ) ∨
      (∃ y : SSet.stdSimplex.obj n ⟶ Y,
        y ≫ (coprod.inl : Y ⟶ Y ⨿ Z) ≫ simplicialEnds f g = σ) ∨
        ∃ z : SSet.stdSimplex.obj n ⟶ Z,
          z ≫ (coprod.inr : Z ⟶ Y ⨿ Z) ≫ simplicialEnds f g = σ := by
  obtain ⟨c, hc⟩ | ⟨y, hy⟩ | ⟨z, hz⟩ :=
    simplex_eq_cylinder_or_left_or_right f g (op n) (SSet.yonedaEquiv σ)
  · exact Or.inl ⟨SSet.yonedaEquiv.symm c, by
      rw [SSet.yonedaEquiv_symm_comp, hc, Equiv.symm_apply_apply]⟩
  · exact Or.inr (Or.inl ⟨SSet.yonedaEquiv.symm y, by
      rw [SSet.yonedaEquiv_symm_comp, hy, Equiv.symm_apply_apply]⟩)
  · exact Or.inr (Or.inr ⟨SSet.yonedaEquiv.symm z, by
      rw [SSet.yonedaEquiv_symm_comp, hz, Equiv.symm_apply_apply]⟩)

end TopCat.DoubleCylinder
