/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.FilteredRealization.CoconeWeakEquivalence
public import Colib.Topology.Realization.MorphismProperty
public import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition

/-!
# Transfinite compositions of realization weak equivalences

At a successor, compose the actual weak equivalences. At a limit, use
filtered-colimit invariance on the original cocone legs.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty

universe u

namespace SSet

private theorem realizationWeakEquivalences_map_of_successors
    {J : Type u} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
    (F : J ⥤ SSet.{u}) [F.IsWellOrderContinuous]
    (h : ∀ j : J, ¬ IsMax j →
      realizationWeakEquivalences (F.map (homOfLE (Order.le_succ j))))
    (j : J) : ∀ (i : J) (f : i ⟶ j), realizationWeakEquivalences (F.map f) := by
  induction j using SuccOrder.limitRecOn with
  | isMin j hj =>
    intro i f
    obtain rfl := hj.eq_of_le (leOfHom f)
    have hf : f = 𝟙 _ := Subsingleton.elim _ _
    rw [hf, F.map_id]
    exact realizationWeakEquivalences.id_mem _
  | succ j hj ih =>
    intro i f
    by_cases e : i = Order.succ j
    · subst i
      have hf : f = 𝟙 _ := Subsingleton.elim _ _
      rw [hf, F.map_id]
      exact realizationWeakEquivalences.id_mem _
    · have hi : i ≤ j := Order.le_of_lt_succ (lt_of_le_of_ne (leOfHom f) e)
      have hf : f = homOfLE hi ≫ homOfLE (Order.le_succ j) := Subsingleton.elim _ _
      rw [hf, F.map_comp]
      exact realizationWeakEquivalences.comp_mem _ _ (ih i (homOfLE hi)) (h j hj)
  | isSuccLimit j hj ih =>
    intro i f
    by_cases e : i = j
    · subst i
      have hf : f = 𝟙 _ := Subsingleton.elim _ _
      rw [hf, F.map_id]
      exact realizationWeakEquivalences.id_mem _
    · have hi : i < j := lt_of_le_of_ne (leOfHom f) e
      let D := (Set.principalSegIio j).monotone.functor ⋙ F
      let c := (Set.principalSegIio j).cocone F
      let : Nonempty (Set.Iio j) := ⟨⟨i, hi⟩⟩
      have hw {a b : Set.Iio j} (g : a ⟶ b) : IsRealizationWeakEquivalence (D.map g) :=
        ih b.1 b.2 a.1 ((Set.principalSegIio j).monotone.functor.map g)
      have hleg := Topology.FilteredRealization.isRealizationWeakEquivalence_coconeLeg D c
        (F.isColimitOfIsWellOrderContinuous j hj) hw ⟨i, hi⟩
      have hf : f = homOfLE hi.le := Subsingleton.elim _ _
      rw [hf]
      exact hleg

instance realizationWeakEquivalences_isStableUnderTransfiniteCompositionOfShape
    (J : Type u) [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J] :
    realizationWeakEquivalences.{u}.IsStableUnderTransfiniteCompositionOfShape J where
  le X Y f hf := by
    obtain ⟨t⟩ := hf
    let c : Cocone t.F := Cocone.mk Y t.incl
    have hw {a b : J} (g : a ⟶ b) : IsRealizationWeakEquivalence (t.F.map g) :=
      realizationWeakEquivalences_map_of_successors t.F t.map_mem b a g
    have hleg : realizationWeakEquivalences (t.incl.app ⊥) :=
      Topology.FilteredRealization.isRealizationWeakEquivalence_coconeLeg t.F c t.isColimit hw ⊥
    rw [← t.fac]
    exact realizationWeakEquivalences.comp_mem _ _
      (realizationWeakEquivalences_of_isIso _) hleg

end SSet
