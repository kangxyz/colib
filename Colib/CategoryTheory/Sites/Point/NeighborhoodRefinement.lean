/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Sites.Point.OfIsCofiltered

/-!
# Refining a neighborhood into a sieve

A lift of a germ along an arrow of a sieve gives a refinement of its representing
neighborhood whose map belongs to the sieve.
-/

@[expose] public section

universe w v v' u u'

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C]
  {N : Type u'} [Category.{v'} N] [InitiallySmall.{w} N] [IsCofiltered N]
  {p : N ⥤ C}

/-- If a germ represented by `f` lifts along an arrow of `R`, some refinement of `f`
belongs to `R`. -/
theorem exists_mem_sieve_of_fiber_map_eq_fiberMk
    {U : N} {X Y : C} {R : Sieve X} {f : p.obj U ⟶ X} {g : Y ⟶ X}
    (hg : R g) {y : (fiber.{w} p).obj Y}
    (h : (fiber.{w} p).map g y = fiberMk.{w} f) :
    ∃ (V : N) (q : V ⟶ U), R (p.map q ≫ f) := by
  obtain ⟨W, a, rfl⟩ := fiberMk_jointly_surjective y
  obtain ⟨T, r, s, -⟩ := IsCofilteredOrEmpty.cone_objs U W
  have hT : fiberMk.{w} (p.map r ≫ f) = fiberMk.{w} (p.map s ≫ (a ≫ g)) := by
    simpa only [fiberMk_map_comp, fiber_map_fiberMk] using h.symm
  obtain ⟨V, q, hq⟩ := exists_of_fiberMk_eq_fiberMk hT
  refine ⟨V, q ≫ r, ?_⟩
  rw [Functor.map_comp, Category.assoc, hq]
  simpa only [Category.assoc] using R.downward_closed hg (p.map q ≫ p.map s ≫ a)

end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
