/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import StacksFrontier.Algebra.Category.ModuleCat.Monoidal.LargeUniverse
public import Mathlib.RingTheory.Flat.CategoryTheory

/-! # Exact tensoring with flat modules in a larger carrier universe -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory
universe u v
namespace ModuleCat
variable {R : Type u} [CommRing R]

/-- The native large-universe tensor with a flat module is left exact. -/
theorem preservesFiniteLimits_tensorRight_large
    (M : ModuleCat.{max u v} R) [Module.Flat R M] :
    PreservesFiniteLimits (tensorRight M) := by
  have h : PreservesFiniteLimits (tensorRight M) ∧ PreservesFiniteColimits (tensorRight M) := by
    apply ((Functor.exact_tfae (tensorRight M)).out 2 4).mp
    intro S hS
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢
    exact Module.Flat.rTensor_exact M hS
  exact h.1

end ModuleCat
