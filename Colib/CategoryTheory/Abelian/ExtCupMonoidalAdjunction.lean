/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.CategoryTheory.Abelian.ExtCupProduct
public import Mathlib.CategoryTheory.Monoidal.Functor

/-! # Unit-source Ext classes and an exact monoidal adjunction

These identities use the existing ExtCup.mapUnit.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory
open Functor.LaxMonoidal
universe w
namespace Colib.ExtCup

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [MonoidalCategory C] [MonoidalCategory D] [HasExt.{w} C] [HasExt.{w} D]
  (L : C ⥤ D) (R : D ⥤ C) [L.Monoidal] [R.LaxMonoidal]
  [L.Additive] [R.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  (adj : L ⊣ R) [adj.IsMonoidal]

omit [Abelian C] [Abelian D] [HasExt.{w} C] [HasExt.{w} D]
  [L.Additive] [R.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R] in
/-- The two lax-unit comparisons recover the original adjunction unit. -/
theorem unit_eq_lax_units :
    adj.unit.app (𝟙_ C) = ε R ≫ R.map (ε L) := by
  rw [Adjunction.IsMonoidal.leftAdjoint_ε (adj := adj), Category.assoc,
    ← R.map_comp, Functor.Monoidal.η_ε, R.map_id]
  exact (Category.comp_id _).symm

/-- Restriction and direct image of a unit-source Ext class is composition with
the original adjunction unit, in every degree. -/
theorem mapUnit_mapUnit [EnoughInjectives C] {F : C} {i : ℕ}
    (a : Ext.{w} (𝟙_ C) F i) :
    Stacks.ExtCup.mapUnit R (Stacks.ExtCup.mapUnit L a) =
      a.comp (Ext.mk₀ (adj.unit.app F)) (add_zero i) := by
  have key := Stacks.ExtFunctorial.mk₀_comp_mapExactFunctor adj.unit (𝟙_ C) i a
  rw [Stacks.ExtFunctorial.mapExactFunctor_id] at key
  simp only [Stacks.ExtCup.mapUnit, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀, ← Ext.comp_assoc_of_second_deg_zero,
    Ext.mk₀_comp_mk₀]
  rw [← unit_eq_lax_units L R adj,
    Stacks.ExtFunctorial.mapExactFunctor_comp_functor]
  exact key

end Colib.ExtCup
