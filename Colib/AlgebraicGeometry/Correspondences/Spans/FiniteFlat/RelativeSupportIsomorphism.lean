/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.FiniteOpenRestriction
public import Colib.AlgebraicGeometry.Correspondences.Spans.FiniteFlat.Isomorphism
public import Colib.AlgebraicGeometry.Correspondences.Spans.FiniteFlat.RelativeSupport

/-!
# Isomorphisms of finite-flat supports on a relative product

The whole relative support span is preserved by an isomorphism that
identifies its two scheme maps. The finite pushforwards therefore carry
the same fundamental cycle.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace AlgebraicGeometry.Cor

/-- An isomorphism of the entire support preserving both legs preserves the relative span. -/
theorem ofFiniteFlatSpanRaw_eq_of_iso
    {S X Y D E : Scheme.{u}} [IsNoetherian X]
    (a : X ⟶ S) (b : Y ⟶ S) [IsSeparated b] [LocallyOfFiniteType b]
    (e : D ≅ E)
    (f : D ⟶ X) [IsFinite f] [Flat f] (g : D ⟶ Y) (h : f ≫ a = g ≫ b)
    (f' : E ⟶ X) [IsFinite f'] [Flat f'] (g' : E ⟶ Y) (h' : f' ≫ a = g' ≫ b)
    (hf : e.hom ≫ f' = f) (hg : e.hom ≫ g' = g) :
    ofFiniteFlatSpanRaw a b f g h = ofFiniteFlatSpanRaw a b f' g' h' := by
  have finitePair {P : Scheme.{u}} (p : P ⟶ X) [IsFinite p] (q : P ⟶ Y)
      (hP : p ≫ a = q ≫ b) : IsFinite (pullback.lift p q hP) := by
    let m := pullback.lift p q hP
    let : IsFinite (m ≫ pullback.fst a b) :=
      isFinite_of_spanLeg_eq (pullback.lift_fst p q hP) (inferInstanceAs (IsFinite p))
    exact IsFinite.of_comp m (pullback.fst a b)
  let m := pullback.lift f g h
  let n := pullback.lift f' g' h'
  let : IsFinite m := finitePair f g h
  let : IsFinite n := finitePair f' g' h'
  let : IsNoetherian D := Scheme.isNoetherian_of_finiteType f
  let : IsNoetherian E := Scheme.isNoetherian_of_finiteType f'
  have he : e.hom ≫ n = m := by
    apply pullback.hom_ext
    · simpa only [m, n, Category.assoc, pullback.lift_fst] using hf
    · simpa only [m, n, Category.assoc, pullback.lift_snd] using hg
  apply Subtype.ext
  change finiteCyclePushforward m (AlgebraicCycle.fundamentalCycle D) =
    finiteCyclePushforward n (AlgebraicCycle.fundamentalCycle E)
  rw [← finiteCyclePushforward_fundamentalCycle_iso e, finiteCyclePushforward_comp_apply]
  exact finiteCyclePushforward_congr m (e.hom ≫ n) he.symm (AlgebraicCycle.fundamentalCycle D)

end AlgebraicGeometry.Cor
