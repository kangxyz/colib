/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Realization.FiniteSubcomplex
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Realized images in a pullback of simplicial monomorphisms

An equality in the realization of the common target is detected by the
original simplicial intersection. This is the compact boundary comparison
used in the bounded cofibration argument of Jardine, *Simplicial presheaves*,
Lemma 2.4, pp. 65–66. https://doi.org/10.1016/0022-4049(87)90100-9
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology
open scoped Simplicial

universe u

namespace SSet

private theorem realization_range_eq_subcomplexRange {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f] :
    Set.range (SSet.toTop.map f) = realizationSubcomplexRange (Subcomplex.range f) := by
  let e := SSet.toTop.mapIso (asIso (Subcomplex.toRange f))
  have h : e.hom ≫ SSet.toTop.map (Subcomplex.range f).ι = SSet.toTop.map f := by
    change SSet.toTop.map (Subcomplex.toRange f) ≫ SSet.toTop.map (Subcomplex.range f).ι =
      SSet.toTop.map f
    rw [← Functor.map_comp]
    exact congrArg SSet.toTop.map (Subcomplex.toRange_ι f)
  apply Set.Subset.antisymm
  · rintro y ⟨x, rfl⟩
    exact ⟨e.hom x, ConcreteCategory.congr_hom h x⟩
  · rintro y ⟨z, rfl⟩
    refine ⟨e.inv z, (ConcreteCategory.congr_hom h (e.inv z)).symm.trans ?_⟩
    exact congrArg (SSet.toTop.map (Subcomplex.range f).ι)
      (ConcreteCategory.congr_hom e.inv_hom_id z)

private theorem range_comp_eq_intersection_of_isPullback
    {P X Y Z : SSet.{u}} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (sq : IsPullback a b f g) :
    Subcomplex.range (a ≫ f) = Subcomplex.range f ⊓ Subcomplex.range g := by
  ext n z
  constructor
  · rintro ⟨p, rfl⟩
    refine ⟨⟨a.app n p, rfl⟩, b.app n p, ?_⟩
    exact (ConcreteCategory.congr_hom (congr_app sq.w n) p).symm
  · rintro ⟨⟨x, hx⟩, y, hy⟩
    let E := (CategoryTheory.evaluation SimplexCategoryᵒᵖ (Type u)).obj n
    let x' : PUnit ⟶ E.obj X := ↾fun _ => x
    let y' : PUnit ⟶ E.obj Y := ↾fun _ => y
    have h : x' ≫ E.map f = y' ≫ E.map g := by
      apply ConcreteCategory.hom_ext
      intro _
      exact hx.trans hy.symm
    let p := (sq.map E).lift x' y' h
    exact ⟨p PUnit.unit,
      (congrArg (f.app n) (ConcreteCategory.congr_hom
        ((sq.map E).lift_fst x' y' h) PUnit.unit)).trans hx⟩

/-- For a pullback of monomorphisms, the original map from the pullback
realizes onto the intersection of the realized images in the common target. -/
theorem realization_range_intersection_of_isPullback
    {P X Y Z : SSet.{u}} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    [Mono f] [Mono g] (sq : IsPullback a b f g) :
    Set.range (SSet.toTop.map (a ≫ f)) = Set.range (SSet.toTop.map f) ∩
      Set.range (SSet.toTop.map g) := by
  let : Mono a := PullbackCone.mono_fst_of_is_pullback_of_mono sq.isLimit
  rw [realization_range_eq_subcomplexRange (a ≫ f),
    range_comp_eq_intersection_of_isPullback sq, realizationSubcomplexRange_inf,
    ← realization_range_eq_subcomplexRange f, ← realization_range_eq_subcomplexRange g]

end SSet
