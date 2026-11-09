/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.DiscreteSubset

/-!
# Compact subsets of countable final covers

A compact subset of a T1 space with the final topology for countably many maps
is contained in the images of finitely many of those maps. The proof selects
points escaping successively larger finite unions. Every subset of their range
is closed, since its inverse image in each source is a finite union of closed
fibers. Compactness excludes the resulting infinite closed discrete subset.
-/
@[expose] public section

open Set Topology

namespace Topology

variable {X : ℕ → Type*} [∀ n, TopologicalSpace (X n)]
  {Y : Type*} [TopologicalSpace Y] [T1Space Y]

/-- Compact sets in a countable final cover lie in a finite initial union of images. -/
theorem IsCompact.subset_finite_initial_ranges (q : ∀ n, C(X n, Y))
    (hcover : ∀ y, ∃ n, y ∈ range (q n))
    (hclosed : ∀ s : Set Y, (∀ n, IsClosed (q n ⁻¹' s)) → IsClosed s)
    {K : Set Y} (hK : IsCompact K) :
    ∃ N : ℕ, K ⊆ ⋃ n ≤ N, range (q n) := by
  classical
  by_contra h
  simp only [not_exists, not_subset] at h
  choose x hxK hx using h
  have hescape (n i : ℕ) (hi : i ≤ n) : x n ∉ range (q i) := by
    intro hxi
    exact hx n (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, hxi⟩⟩)
  have hsubclosed (s : Set Y) (hs : s ⊆ range x) : IsClosed s := by
    apply hclosed
    intro i
    have heq : q i ⁻¹' s = ⋃ j ∈ Finset.range i, q i ⁻¹' ({x j} ∩ s) := by
      ext z
      constructor
      · intro hz
        obtain ⟨j, hj⟩ := hs hz
        have hji : j < i := by
          by_contra hn
          exact hescape j i (Nat.le_of_not_gt hn) ⟨z, hj.symm⟩
        exact mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨Finset.mem_range.mpr hji,
          ⟨hj.symm, hz⟩⟩⟩
      · intro hz
        obtain ⟨j, hj, hz⟩ := mem_iUnion₂.mp hz
        exact hz.2
    rw [heq]
    exact isClosed_biUnion_finset fun j _ ↦
      ((finite_singleton (x j)).subset inter_subset_left).isClosed.preimage (q i).continuous
  have hcompact : IsCompact (range x) :=
    hK.of_isClosed_subset (hsubclosed _ Subset.rfl) (range_subset_iff.mpr hxK)
  have hfinite : (range x).Finite := hcompact.finite
    (isDiscrete_iff_forall_mem_exists_isClosed.mpr fun s hs ↦
      ⟨s, hsubclosed s hs, inter_eq_left.mpr hs⟩)
  choose index hindex using hcover
  obtain ⟨N, hN⟩ := (hfinite.image index).bddAbove
  have hxN : x N ∈ range x := mem_range_self N
  exact hescape N (index (x N)) (hN (mem_image_of_mem index hxN)) (hindex (x N))

end Topology
