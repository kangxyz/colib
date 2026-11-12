/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalEquiconnection
public import Mathlib.Topology.Connected.PathConnected

/-!
# Actual local connectors give open path components

The open section of the connector domain at each point is joined to that
point by the displayed connector. These sections prove openness of every
path component directly, without realization domination or any CW assertion.
-/

open Topology

/-! Implementation source: `Quillen/Topology/LocalEquiconnection/OpenComponents.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps and proofs are retained. -/

@[expose] public section
noncomputable section
open scoped Topology unitInterval
universe u
namespace Topology.LocalEquiconnection

variable {A : Type u} [TopologicalSpace A] (E : LocalEquiconnection A)

/-- An allowed pair has the actual path supplied by the local connector. -/
def pairPath (x y : A) (h : (x, y) ∈ E.domain) : Path x y where
  toFun t := E.connector (⟨(x, y), h⟩, t)
  continuous_toFun := E.connector.continuous.comp (continuous_const.prodMk continuous_id)
  source' := E.connector_zero ⟨(x, y), h⟩
  target' := E.connector_one ⟨(x, y), h⟩

include E in
/-- Every path component is open, using open sections of the actual connector domain. -/
theorem isOpen_pathComponent (x : A) : IsOpen (pathComponent x) := by
  apply isOpen_iff_forall_mem_open.mpr
  intro y hxy
  refine ⟨{z | (y, z) ∈ E.domain}, ?_, ?_, E.diagonal_mem y⟩
  · intro z hz
    exact hxy.trans ⟨E.pairPath y z hz⟩
  · exact E.isOpen_domain.preimage (continuous_const.prodMk continuous_id)

end Topology.LocalEquiconnection
