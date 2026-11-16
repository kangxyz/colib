/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.CWComplex.ThinNeighborhoods
public import Colib.Topology.Covering.PathClassSimplyConnected

/-!
# Simply connected covers of actual connected classical CW subtypes

The source of the covering is the existing literal path-class total space with
its actual chart-generated topology. Its local geometric input is constructed
from the original CW cells and quotient topology, not supplied as a hypothesis.
Covering, surjectivity and simple connectedness are proved separately.

Adapted from `Quillen/Topology/CWComplex/SimplyConnectedCover.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public section

open Topology
noncomputable section
open Set
universe u
namespace Topology.CWComplex
variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable (C : Set X) [CWComplex C] [ConnectedSpace C]

/-- Every actual connected Hausdorff classical CW subtype has a same-universe
surjective covering with genuinely simply connected total space. -/
theorem exists_simplyConnected_cover :
    ∃ (E : Type u) (_ : TopologicalSpace E) (p : C(E, C)),
      IsCoveringMap p ∧ Function.Surjective p ∧ SimplyConnectedSpace E := by
  let := locallyPathConnectedSpace C
  let : PathConnectedSpace C := PathConnectedSpace.of_locallyPathConnectedSpace
  let b : C := Classical.choice inferInstance
  let A := pathThinNeighborhoods C
  let := (A.prebundle b).totalSpaceTopology
  exact ⟨PathThinNeighborhoods.Total b, inferInstance, A.totalProjection b,
    A.isCoveringMap_projection b, PathThinNeighborhoods.projection_surjective b,
    A.total_simplyConnectedSpace b⟩

end Topology.CWComplex
