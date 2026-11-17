/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import StacksFrontier.CategoryTheory.Abelian.ExtCupProduct
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-! # The right unit for the native Ext cup product -/
@[expose] public noncomputable section
universe w v u
namespace Stacks.ExtCup
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory
variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [HasExt.{w} C]
  [EnoughInjectives C] [(tensorRight (𝟙_ C)).Additive]
  [PreservesFiniteLimits (tensorRight (𝟙_ C))]
  [PreservesFiniteColimits (tensorRight (𝟙_ C))]

/-- The identity class of the monoidal unit is a right unit for the original cup. -/
theorem cup_right_unit {F : C} {i : ℕ} (a : Ext.{w} (𝟙_ C) F i) :
    cup (ρ_ F).hom a (Ext.mk₀ (𝟙 (𝟙_ C))) (zero_add i) = a := by
  have key := Stacks.ExtFunctorial.mk₀_comp_mapExactFunctor
    (rightUnitorNatIso C).hom (𝟙_ C) i a
  simp only [rightUnitorNatIso_hom_app, Stacks.ExtFunctorial.mapExactFunctor_id] at key
  simp only [cup, Ext.mk₀_comp_mk₀, Category.id_comp]
  rw [← key, ← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀]
  simp [← unitors_equal]
end Stacks.ExtCup
