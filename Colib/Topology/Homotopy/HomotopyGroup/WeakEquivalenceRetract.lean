/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.HomotopyGroup.WeakEquivalenceProperty
public import Mathlib.CategoryTheory.Retract

/-!
# Retracts of weak homotopy equivalences

On path components the chosen target representative is pulled back
through the retract. In every degree the four actual pointed maps
give a retract of the based homotopy-set bijection.
-/

@[expose] public section

open CategoryTheory Topology
open scoped Topology

universe u

namespace Topology

private theorem bijective_basepoint_change {X Y : TopCat.{u}} {g : C(X, Y)}
    (hg : IsWeakHomotopyEquivalence g) {x : X} {y : Y} (h : g x = y) (n : ℕ) :
    Function.Bijective (HomotopyGroup.map (N := Fin n) g h) := by
  subst y
  exact hg.homotopy_bijective x n

/-- Retracts preserve weakness of the original continuous map. -/
theorem IsWeakHomotopyEquivalence.of_retract {A B X Y : TopCat.{u}} {f : A ⟶ B} {g : X ⟶ Y}
    (r : RetractArrow f g) (hg : IsWeakHomotopyEquivalence g.hom) :
    IsWeakHomotopyEquivalence f.hom where
  component_surjective y := by
    obtain ⟨x, hx⟩ := hg.component_surjective (r.i.right y)
    have h₀ := ConcreteCategory.congr_hom r.r_w x
    have h₁ := ConcreteCategory.congr_hom r.retract_right y
    refine ⟨r.r.left x, ?_⟩
    have h := hx.map r.r.right.hom.continuous
    change Joined (r.r.right (g x)) (r.r.right (r.i.right y)) at h
    change f (r.r.left x) = r.r.right (g x) at h₀
    change r.r.right (r.i.right y) = y at h₁
    rw [h₀, ← h₁]
    exact h
  homotopy_bijective x n := by
    let a := r.i.left.hom
    let b := r.r.left.hom
    let c := r.i.right.hom
    let d := r.r.right.hom
    have h₀ : g.hom.comp a = c.comp f.hom := congrArg TopCat.Hom.hom r.i_w
    have h₁ : f.hom.comp b = d.comp g.hom := congrArg TopCat.Hom.hom r.r_w
    have hb : b.comp a = ContinuousMap.id A := congrArg TopCat.Hom.hom r.retract_left
    have hd : d.comp c = ContinuousMap.id B := congrArg TopCat.Hom.hom r.retract_right
    have hbx : b (a x) = x := ContinuousMap.congr_fun hb x
    have hdx : d (c (f x)) = f x := ContinuousMap.congr_fun hd (f x)
    have h₀x : g (a x) = c (f x) := ContinuousMap.congr_fun h₀ x
    let F := HomotopyGroup.map (N := Fin n) f.hom (x := x) rfl
    let G := HomotopyGroup.map (N := Fin n) g.hom h₀x
    let A' := HomotopyGroup.map (N := Fin n) a (x := x) rfl
    let B' := HomotopyGroup.map (N := Fin n) b hbx
    let C' := HomotopyGroup.map (N := Fin n) c (x := f x) rfl
    let D' := HomotopyGroup.map (N := Fin n) d hdx
    have w₀ : G ∘ A' = C' ∘ F := by
      funext t
      dsimp only [G, A', C', F, Function.comp_apply]
      rw [← HomotopyGroup.map_comp, ← HomotopyGroup.map_comp]
      exact congrFun (homotopyGroupMap_congr h₀ _ _) t
    have w₁ : F ∘ B' = D' ∘ G := by
      funext t
      dsimp only [F, B', D', G, Function.comp_apply]
      rw [← HomotopyGroup.map_comp, ← HomotopyGroup.map_comp]
      exact congrFun (homotopyGroupMap_congr h₁ _ _) t
    have hBA : Function.LeftInverse B' A' := by
      intro t
      dsimp only [B', A']
      rw [← HomotopyGroup.map_comp]
      exact (congrFun (homotopyGroupMap_congr hb _ rfl) t).trans (HomotopyGroup.map_id t)
    have hDC : Function.LeftInverse D' C' := by
      intro t
      dsimp only [D', C']
      rw [← HomotopyGroup.map_comp]
      exact (congrFun (homotopyGroupMap_congr hd _ rfl) t).trans (HomotopyGroup.map_id t)
    have hG : Function.Bijective G := bijective_basepoint_change hg h₀x n
    change Function.Bijective F
    refine ⟨?_, ?_⟩
    · intro s t hst
      apply hBA.injective
      apply hG.injective
      change (G ∘ A') s = (G ∘ A') t
      rw [w₀]
      exact congrArg C' hst
    · intro t
      obtain ⟨s, hs⟩ := hG.2 (C' t)
      refine ⟨B' s, ?_⟩
      change (F ∘ B') s = t
      rw [w₁]
      exact (congrArg D' hs).trans (hDC t)

end Topology
