/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.TelescopeRepresentability

/-!
# Eventual original-stage homotopy in the reduced telescope

A relative homotopy between maps from a compact domain into two original
stages can be realized in a common later original stage. The endpoint maps
are exactly the original finite transition composites. Consequently equality
of the original stage homotopy-group images is detected at a finite later
stage, including the zeroth homotopy set.
-/
@[expose] public section

open Topology


noncomputable section
open CategoryTheory Set Topology
open scoped unitInterval
open unitInterval
universe u v
namespace Topology.LoopPrespectrum.Telescope
variable (E : ℕ → LoopPrespectrum.{u}) (f : ∀ i, E i ⟶ E (i + 1)) (k : ℕ)
  [∀ i, T1Space ((E i).space k)]

/-- A compact-domain relative homotopy is realized between the actual later-stage composites. -/
theorem exists_eventual_homotopy {A : Type v} [TopologicalSpace A] [CompactSpace A]
    {i j : ℕ} (S : Set A) (p : C(A, (E i).space k)) (q : C(A, (E j).space k))
    (H : (((inclusion E f i).map k).comp p).HomotopyRel
      (((inclusion E f j).map k).comp q) S) :
    ∃ N : ℕ, ∃ hi : i ≤ N, ∃ hj : j ≤ N,
      Nonempty ((((transition E f i N hi).map k).comp p).HomotopyRel
        (((transition E f j N hj).map k).comp q) S) := by
  obtain ⟨B, hB⟩ := exists_cylinder_bound E f k H.toHomotopy.toContinuousMap
  let N := max (B + 1) (max i j)
  have hBN : B < N := (Nat.lt_succ_self B).trans_le (le_max_left _ _)
  have hi : i ≤ N := (le_max_left i j).trans (le_max_right _ _)
  have hj : j ≤ N := (le_max_right i j).trans (le_max_right _ _)
  let c := ((collapse E f N).map k).comp H.toHomotopy.toContinuousMap
  have hc (z : I × A) : c z ∈ range ((inclusion E f N).map k) :=
    collapse_mem_stage E f k H.toHomotopy.toContinuousMap hBN hB z
  let L := liftStage E f k N c hc
  have hL (z : I × A) : (inclusion E f N).map k (L z) = (collapse E f N).map k (H z) :=
    inclusion_liftStage E f k N c hc z
  refine ⟨N, hi, hj, ⟨?_⟩⟩
  exact
    { toFun := L
      continuous_toFun := L.continuous
      map_zero_left := fun a ↦ by
        apply inclusion_injective E f k N
        rw [hL, H.apply_zero]
        exact collapse_inclusion E f hi k (p a)
      map_one_left := fun a ↦ by
        apply inclusion_injective E f k N
        rw [hL, H.apply_one]
        exact collapse_inclusion E f hj k (q a)
      prop' := fun t a ha ↦ by
        apply inclusion_injective E f k N
        change (inclusion E f N).map k (L (t, a)) =
          (inclusion E f N).map k ((transition E f i N hi).map k (p a))
        rw [hL, H.eq_fst t ha]
        exact collapse_inclusion E f hi k (p a) }

/-- Based sphere homotopy in the telescope becomes based homotopy at a common original stage. -/
theorem exists_eventual_genLoop_homotopy (n : ℕ) {i j : ℕ}
    (p : GenLoop (Fin n) ((E i).space k) ((E i).point k))
    (q : GenLoop (Fin n) ((E j).space k) ((E j).point k))
    (H : GenLoop.Homotopic
      (GenLoop.postcomp ((inclusion E f i).map k) ((inclusion E f i).map_point k) p)
      (GenLoop.postcomp ((inclusion E f j).map k) ((inclusion E f j).map_point k) q)) :
    ∃ N : ℕ, ∃ hi : i ≤ N, ∃ hj : j ≤ N,
      GenLoop.Homotopic
        (GenLoop.postcomp ((transition E f i N hi).map k) ((transition E f i N hi).map_point k) p)
        (GenLoop.postcomp ((transition E f j N hj).map k)
          ((transition E f j N hj).map_point k) q) := by
  obtain ⟨H⟩ := H
  exact exists_eventual_homotopy E f k (Cube.boundary (Fin n)) p.val q.val H

/-- Equality of original homotopy-group images is detected after finitely many transitions. -/
theorem exists_eventual_homotopyGroup_eq (n : ℕ) {i j : ℕ}
    (a : HomotopyGroup.Pi n ((E i).space k) ((E i).point k))
    (b : HomotopyGroup.Pi n ((E j).space k) ((E j).point k))
    (hab : HomotopyGroup.map ((inclusion E f i).map k) ((inclusion E f i).map_point k) a =
      HomotopyGroup.map ((inclusion E f j).map k) ((inclusion E f j).map_point k) b) :
    ∃ N : ℕ, ∃ hi : i ≤ N, ∃ hj : j ≤ N,
      HomotopyGroup.map ((transition E f i N hi).map k) ((transition E f i N hi).map_point k) a =
        HomotopyGroup.map ((transition E f j N hj).map k)
          ((transition E f j N hj).map_point k) b := by
  induction a using Quotient.inductionOn with
  | h p =>
    induction b using Quotient.inductionOn with
    | h q =>
      obtain ⟨N, hi, hj, H⟩ := exists_eventual_genLoop_homotopy E f k n p q (Quotient.exact hab)
      exact ⟨N, hi, hj, Quotient.sound H⟩

end Topology.LoopPrespectrum.Telescope
