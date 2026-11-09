/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Compactness.CountableFinal
public import Colib.Topology.Prespectrum.TelescopeSeparation

/-!
# Compact images in the original reduced telescope

With T1 stage spaces, every compact subset of the original reduced telescope
lies in finitely many original stage cylinders. In particular this holds for
maps from compact spaces and for their whole compact-parameter homotopies.
The collapsed base ray causes no difficulty: the argument uses the final
quotient topology and closed point fibers, not a height function.

These statements give finite-cylinder support. Deformation to an original
stage and the homotopy-group colimit comparison are separate assertions.
-/
@[expose] public section

open Topology


open CategoryTheory Set Topology
open scoped unitInterval
open unitInterval
universe u v
namespace Topology.LoopPrespectrum.Telescope
variable (E : ℕ → LoopPrespectrum.{u}) (f : ∀ i, E i ⟶ E (i + 1)) (k : ℕ)
  [∀ i, T1Space ((E i).space k)]

/-- Every compact set in the original quotient has finite original-cylinder support. -/
theorem IsCompact.subset_finite_cylinders {K : Set (Space E f k)} (hK : IsCompact K) :
    ∃ N : ℕ, K ⊆ ⋃ i ≤ N, range (cylinder E f k i) := by
  apply Topology.IsCompact.subset_finite_initial_ranges (cylinder E f k)
  · intro q
    induction q using Quot.inductionOn with
    | h z => exact ⟨z.1, z.2, rfl⟩
  · intro s hs
    apply isQuotientMap_quot_mk.isClosed_preimage.mp
    exact isClosed_sigma_iff.mpr hs
  · exact hK

/-- A continuous map from any compact space has uniformly bounded cylinder support. -/
theorem exists_cylinder_bound {A : Type v} [TopologicalSpace A] [CompactSpace A]
    (g : C(A, Space E f k)) :
    ∃ N : ℕ, ∀ a, ∃ i ≤ N, ∃ z, cylinder E f k i z = g a := by
  obtain ⟨N, hN⟩ := IsCompact.subset_finite_cylinders E f k (isCompact_range g.continuous)
  refine ⟨N, fun a ↦ ?_⟩
  obtain ⟨i, hi, z, hz⟩ := mem_iUnion₂.mp (hN (mem_range_self a))
  exact ⟨i, hi, z, hz⟩

/-- One bound works for the entire original interval homotopy, including both endpoints. -/
theorem exists_homotopy_cylinder_bound {A : Type v} [TopologicalSpace A] [CompactSpace A]
    (H : C(I × A, Space E f k)) :
    ∃ N : ℕ, ∀ t a, ∃ i ≤ N, ∃ z, cylinder E f k i z = H (t, a) := by
  obtain ⟨N, hN⟩ := exists_cylinder_bound E f k H
  exact ⟨N, fun t a ↦ hN (t, a)⟩

end Topology.LoopPrespectrum.Telescope
