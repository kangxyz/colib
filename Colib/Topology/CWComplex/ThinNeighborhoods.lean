/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.CWComplex.NeighborhoodContraction
public import Colib.Topology.Covering.LocalConnectorHypotheses

/-!
# Actual ambient-thin neighborhoods of arbitrary classical CW subtypes

The constructed global ambient contractions provide an open neighborhood of
every original point. Actual local path connectedness, already obtained from
the original characteristic quotient, permits passage to its open pathcomponent.
This gives exactly the geometric input for the existing path-class covering.
No local-finiteness, finite-dimensionality or countability assumption occurs.

Adapted from `Quillen/Topology/CWComplex/ThinNeighborhoods.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public section

open Topology
noncomputable section
open Set
universe u
namespace Topology.CWComplex
variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable (C : Set X) [CWComplex C]

/-- Every original point has an actual open neighborhood ambient-contractible
to that precise point through a jointly continuous homotopy. -/
theorem exists_ambientContractionNeighborhood (x : C) :
    ∃ U : Set C, IsOpen U ∧ x ∈ U ∧
      Nonempty ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, C)).Homotopy
        (ContinuousMap.const U x)) := by
  obtain ⟨n, i, y, hy⟩ := exists_cellNeighborhood C x
  have he : cellNeighborhoodToComplex C n i y = x := Subtype.ext hy
  refine ⟨neighborhoodSet C n i, isOpen_neighborhoodSet C n i, ?_, ?_⟩
  · rw [← he]
    exact seed_mem_neighborhoodSet C n i y
  · have H := neighborhoodAmbientContraction C n i y
    rw [he] at H
    exact ⟨H⟩

/-- Ambient contraction implies ambient uniqueness of relative endpoint path classes. -/
theorem exists_open_ambientPathThin (x : C) :
    ∃ U : Set C, IsOpen U ∧ x ∈ U ∧ AmbientPathThin U := by
  obtain ⟨U, hU, hx, ⟨H⟩⟩ := exists_ambientContractionNeighborhood C x
  exact ⟨U, hU, hx, ambientPathThin_of_constant_homotopy x H.symm⟩

/-- The actual CW topology supplies open pathconnected ambient-thin neighborhoods. -/
def pathThinNeighborhoods : PathThinNeighborhoods C := by
  letI := locallyPathConnectedSpace C
  let U : C → Set C := fun x ↦ Classical.choose (exists_open_ambientPathThin C x)
  have hU (x : C) : IsOpen (U x) ∧ x ∈ U x ∧ AmbientPathThin (U x) :=
    Classical.choose_spec (exists_open_ambientPathThin C x)
  exact
    { neighborhood x := pathComponentIn (U x) x
      isOpen_neighborhood x := (hU x).1.pathComponentIn x
      mem_neighborhood x := mem_pathComponentIn_self (hU x).2.1
      isPathConnected_neighborhood x := isPathConnected_pathComponentIn (hU x).2.1
      ambientPathThin x := (hU x).2.2.mono pathComponentIn_subset }

end Topology.CWComplex
