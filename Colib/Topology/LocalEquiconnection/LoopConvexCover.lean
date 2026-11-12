/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalEquiconnection.Loops
public import Colib.Topology.PathSpace.Metric
public import Mathlib.Topology.ShrinkingLemma

/-!
# Connector-convex open neighborhoods in the original based loop space

Shrink a finite subcover of the interval to a finite compact cover. Requiring
each compact piece to map into its assigned open convex carrier is a genuine
compact-open condition. The pieces cover every loop time, so every pair of
loops in the resulting neighborhood lies in the loop connector domain, and
the pointwise connector stays in the same neighborhood.
-/

open Topology

/-! Implementation source: `Quillen/Topology/LocalEquiconnection/LoopConvexCover.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps and proofs are retained. -/

@[expose] public section
noncomputable section

open scoped Topology unitInterval

universe u v
namespace Topology.LocalEquiconnection

variable {A : Type u} [TopologicalSpace A] (E : LocalEquiconnection A) (p : A)

/-- A finite family of compact-open carrier conditions on the original loop space. -/
def loopCarrier {κ : Type v} (K : κ → Set I) (V : κ → Set A) : Set (Path p p) :=
  {γ | ∀ i, Set.MapsTo γ (K i) (V i)}

/-- Finite compact-open carrier conditions define an open set of original loops. -/
theorem isOpen_loopCarrier {κ : Type v} [Finite κ] (K : κ → Set I) (V : κ → Set A)
    (hK : ∀ i, IsCompact (K i)) (hV : ∀ i, IsOpen (V i)) :
    IsOpen (loopCarrier p K V) := by
  have h : ∀ i, IsOpen {γ : Path p p | Set.MapsTo γ (K i) (V i)} := fun i ↦
    (ContinuousMap.isOpen_setOfPred_mapsTo (hK i) (hV i)).preimage
      PathSpace.continuous_toContinuousMap
  simpa only [loopCarrier, Set.ofPred_forall] using isOpen_iInter_of_finite h

/-- A covering family of connector-convex carriers gives a convex set of loops. -/
theorem isConvex_loopCarrier {κ : Type v} (K : κ → Set I) (V : κ → Set A)
    (hcover : Set.univ ⊆ ⋃ i, K i) (hV : ∀ i, E.IsConvex (V i)) :
    (E.loops p).IsConvex (loopCarrier p K V) where
  pair_mem {γ δ} hγ hδ s := by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover (Set.mem_univ s))
    exact (hV i).pair_mem (hγ i hi) (hδ i hi)
  connector_mem {γ δ} hγ hδ t i s hs :=
    (hV i).connector_mem (hγ i hs) (hδ i hs) t

/-- An open connector-convex cover of the target gives such a neighborhood of every based loop. -/
theorem exists_convex_open_loop_neighborhood {κ : Type v} (V : κ → Set A)
    (hopen : ∀ i, IsOpen (V i)) (hconvex : ∀ i, E.IsConvex (V i))
    (hcover : ∀ a, ∃ i, a ∈ V i) (γ : Path p p) :
    ∃ W : Set (Path p p), IsOpen W ∧ γ ∈ W ∧ (E.loops p).IsConvex W := by
  classical
  let U : κ → Set I := fun i ↦ γ ⁻¹' V i
  have hu : ∀ i, IsOpen (U i) := fun i ↦ (hopen i).preimage γ.continuous
  have huc : Set.univ ⊆ ⋃ i, U i := by
    intro t _
    obtain ⟨i, hi⟩ := hcover (γ t)
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hu huc
  have hs' : Set.univ ⊆ ⋃ i : s, U i.1 := by
    intro t ht
    obtain ⟨i, hi, hit⟩ := Set.mem_iUnion₂.mp (hs ht)
    exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hit⟩
  obtain ⟨K, hKcover, _, hKU, hKcompact⟩ :=
    exists_subset_iUnion_compact_subset_t2space isCompact_univ
      (fun i : s ↦ hu i.1) (fun _ _ ↦ Set.toFinite _) hs'
  refine ⟨loopCarrier p K (fun i : s ↦ V i.1),
    isOpen_loopCarrier p K _ hKcompact (fun i ↦ hopen i.1), ?_, ?_⟩
  · intro i t ht
    exact hKU i ht
  · exact isConvex_loopCarrier E p K _ hKcover (fun i ↦ hconvex i.1)

end Topology.LocalEquiconnection
