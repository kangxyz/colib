/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Mathlib.Topology.Homotopy.HSpaces
public import Colib.Topology.ClassifyingSpace.NaturalTransformationTracks
public import Colib.Topology.Homotopy.HomotopyGroup.PathTransportHomotopy
public import Colib.Topology.Homotopy.HomotopyGroup.PathTransportComposition

/-!
# Moving-basepoint transport at an H-space unit

The actual multiplication and its based unit homotopies make every loop at
an H-space unit act trivially on every finite homotopy group. A displayed
path transfers this property to another basepoint. An actual continuous map
injective on the specified homotopy group then detects the same property in
its source. No connectedness or homotopy-commutativity hypothesis is needed.
The current consumer is the original Q-space action in `KTheory.SpaceAction`.
-/
/-! Implementation provenance: `Quillen/Topology/HomotopyGroups/HSpaceAction.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining actual paths and normalization. -/
@[expose] public section

noncomputable section
open HomotopyGroup
open scoped Topology unitInterval
universe u v
namespace Topology

/-- Actual moving-basepoint transport is trivial at the unit of an H-space. -/
theorem hSpace_pathTransport_loop {X : Type u} [TopologicalSpace X] [HSpace X]
    (p : Path (HSpace.e : X) HSpace.e) (n : ℕ)
    (a : HomotopyGroup.Pi n X HSpace.e) : pathTransport p n a = a := by
  let e : X := HSpace.e
  let L : C(X, X) := HSpace.hmul.comp ((ContinuousMap.const X e).prodMk (ContinuousMap.id X))
  let R : C(X, X) := HSpace.hmul.comp ((ContinuousMap.id X).prodMk (ContinuousMap.const X e))
  have hL : L e = e := HSpace.hmul_e_e
  have hR : R e = e := HSpace.hmul_e_e
  let q : Path e e := (p.map R.continuous).cast hR.symm hR.symm
  let H : L.Homotopy L := {
    toFun := fun z => HSpace.hmul (p z.1, z.2)
    continuous_toFun := HSpace.hmul.continuous.comp
      ((p.continuous.comp continuous_fst).prodMk continuous_snd)
    map_zero_left := by
      intro z
      change HSpace.hmul (p 0, z) = HSpace.hmul (e, z)
      rw [p.source]
    map_one_left := by
      intro z
      change HSpace.hmul (p 1, z) = HSpace.hmul (e, z)
      rw [p.target] }
  have htrack : ((H.evalAt e).cast hL.symm hL.symm) = q := by ext t; rfl
  have ht := pathTransport_homotopyGroupMap_homotopy_cast H e hL hL n a
  rw [htrack] at ht
  have hmap : HomotopyGroup.map L hL a = a := by
    have hh := HomotopyGroup.map_eq_of_based_homotopy (N := Fin n)
      hL (rfl : (ContinuousMap.id X) e = e) HSpace.eHmul.toHomotopy
      (fun t => HSpace.eHmul.eq_snd t (show e ∈ ({HSpace.e} : Set X) from rfl))
    exact (congrFun hh a).trans (HomotopyGroup.map_id a)
  rw [hmap] at ht
  have hq : q.Homotopic p := by
    refine ⟨{ toHomotopy := HSpace.hmulE.toHomotopy.compContinuousMap p.toContinuousMap
              prop' := ?_ }⟩
    intro t s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · change HSpace.hmulE (t, p 0) = R (p 0)
      rw [p.source]
      exact HSpace.hmulE.eq_fst t rfl
    · change HSpace.hmulE (t, p 1) = R (p 1)
      rw [p.target]
      exact HSpace.hmulE.eq_fst t rfl
  rw [pathTransport_eq_of_homotopic hq] at ht
  exact ht

/-- Trivial loop transport moves along a displayed path; no choice of a component
representative or homotopy commutativity is assumed. -/
theorem pathTransport_loop_trivial_of_path
    {X : Type u} [TopologicalSpace X] {x y : X} (γ : Path x y) (n : ℕ)
    (hy : ∀ p : Path y y, ∀ a : HomotopyGroup.Pi n X y, pathTransport p n a = a)
    (p : Path x x) (a : HomotopyGroup.Pi n X x) : pathTransport p n a = a := by
  apply (pathTransport γ n).injective
  have h := hy ((γ.symm.trans p).trans γ) (pathTransport γ n a)
  rw [pathTransport_trans, pathTransport_trans, pathTransport_symm_apply] at h
  exact h

/-- An actual map injective on the specified homotopy group reflects triviality
of the action; the target basepoint may be joined to the H-space unit. -/
theorem pathTransport_loop_trivial_of_hSpace_detection
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] [HSpace Y]
    (f : C(X, Y)) (x : X) (γ : Path (f x) HSpace.e) (n : ℕ)
    (hf : Function.Injective (HomotopyGroup.map (N := Fin n) f (x := x) rfl))
    (p : Path x x) (a : HomotopyGroup.Pi n X x) : pathTransport p n a = a := by
  apply hf
  have hn := pathTransport_naturality f p n a
  have ht := pathTransport_loop_trivial_of_path γ n (fun q b => hSpace_pathTransport_loop q n b)
    (p.map f.continuous) (HomotopyGroup.map f rfl a)
  exact hn.symm.trans ht

end Topology

attribute [colib_ref "quillen"
  "Quillen/Topology/HomotopyGroups/HSpaceAction.lean:31-98"
  "adaptation" "Original maps, whole tracks, native model comparisons and signs"]
  Topology.hSpace_pathTransport_loop
  Topology.pathTransport_loop_trivial_of_path
  Topology.pathTransport_loop_trivial_of_hSpace_detection
