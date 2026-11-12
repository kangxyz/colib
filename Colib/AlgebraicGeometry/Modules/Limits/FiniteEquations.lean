/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.EventualMapEq

/-!
# Simultaneous module equations at one stage

A finite family of equalities between pullbacks of finitely presented module morphisms holds
at one common stage. The common refinement is taken in the over category of the original stage,
so every equality uses the same transition morphism, rather than unrelated maps to that stage.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe v u w

namespace Stacks.AlgebraicGeometry.ModuleLimits

/-- Finitely many equations between module morphisms which hold on a cofiltered limit already
hold after one common transition. The modules may vary with the equation. -/
theorem exists_pullback_map_eq_of_isLimit_finite {I : Type u} [Category.{v} I]
    [IsCofiltered I] (D : I ⥤ Scheme.{u})
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    (c : Cone D) (hc : IsLimit c) (i : I) [CompactSpace (D.obj i)]
    {κ : Type w} [Finite κ] (F G : κ → (D.obj i).Modules)
    [∀ a, (F a).IsFinitePresentation] [∀ a, (G a).IsFinitePresentation]
    (f g : ∀ a, F a ⟶ G a)
    (h : ∀ a, (Scheme.Modules.pullback (c.π.app i)).map (f a) =
      (Scheme.Modules.pullback (c.π.app i)).map (g a)) :
    ∃ (j : I) (e : j ⟶ i), ∀ a,
      (Scheme.Modules.pullback (D.map e)).map (f a) =
        (Scheme.Modules.pullback (D.map e)).map (g a) := by
  classical
  let := Fintype.ofFinite κ
  choose j e he using fun a =>
    exists_pullback_map_eq_of_isLimit' D c hc i (F a) (G a) (f a) (g a) (h a)
  let k (a : κ) : Over i := Over.mk (e a)
  obtain ⟨l, hl⟩ := IsCofiltered.inf_objs_exists (Finset.image k Finset.univ)
  have m (a : κ) : l ⟶ k a :=
    (hl (Finset.mem_image_of_mem k (Finset.mem_univ a))).some
  refine ⟨l.left, l.hom, fun a => ?_⟩
  have hcomp : (m a).left ≫ e a = l.hom := Over.w (m a)
  have hh := pullback_map_eq_of_precomp (D.map (m a).left) (D.map (e a)) (he a)
  rwa [← D.map_comp, hcomp] at hh

end Stacks.AlgebraicGeometry.ModuleLimits
