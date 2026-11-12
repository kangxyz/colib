/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.MetricOrderComplex.LocalEquiconnection
public import Colib.Topology.LocalEquiconnection.LoopConvexCover

/-!
# Metric and equi-local convexity of the actual metric-order based loop space

The previously proved common-support connector supplies the generic geometric
contract. Pointwise looping preserves the original Path topology and all
endpoint/diagonal equations. Finite compact-open star conditions give actual
open connector-convex neighborhoods of every loop. The compatible metric is
the original compact-open sup metric, and its connector domain is distance <2.
No realization domination or CW-type conclusion is asserted.
-/

open Topology

/-! Implementation source: `Quillen/Topology/MetricOrderComplex/LoopEquiconnection.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The existing base-space connector is reused; the original loop maps and proofs are retained. -/

@[expose] public section
noncomputable section

open scoped Topology unitInterval

universe u
namespace Topology.MetricOrderComplex

variable {P : Type u} [PartialOrder P]

/-- The actual compact-open based loop space has a diagonal-fixed local connector. -/
def loopEquiconnection (p : P) : LocalEquiconnection (Path (vertex p) (vertex p)) :=
  localEquiconnection.loops (vertex p)

/-- The pointwise common-support domain is exactly distance <2 in the compatible sup metric. -/
theorem loop_domain_iff_dist_lt_two (p : P) (γ δ : Path (vertex p) (vertex p)) :
    (γ, δ) ∈ (loopEquiconnection p).domain ↔ dist γ δ < 2 := by
  change (∀ t : I, 0 < commonMass (γ t) (δ t)) ↔ _
  rw [PathSpace.dist_lt_iff]
  exact forall_congr' fun t ↦ commonMass_pos_iff_dist_lt_two (γ t) (δ t)

/-- Evaluation gives the unchanged pointwise common-support connector. -/
theorem loop_connector_apply (p : P) (z : (loopEquiconnection p).domain) (t s : I) :
    (loopEquiconnection p).connector (z, t) s =
      connectorPath (z.1.1 s) (z.1.2 s) (z.2 s) t := rfl

/-- The original constant based loop is fixed at every connector time. -/
theorem loop_connector_refl (p : P) (t : I) :
    (loopEquiconnection p).connector
      (⟨(Path.refl (vertex p), Path.refl (vertex p)),
        (loopEquiconnection p).diagonal_mem _⟩, t) = Path.refl (vertex p) :=
  (loopEquiconnection p).connector_diagonal _ t

/-- Every original based loop has an open connector-convex neighborhood. -/
theorem exists_convex_open_loop_neighborhood (p : P) (γ : Path (vertex p) (vertex p)) :
    ∃ W : Set (Path (vertex p) (vertex p)),
      IsOpen W ∧ γ ∈ W ∧ (loopEquiconnection p).IsConvex W :=
  localEquiconnection.exists_convex_open_loop_neighborhood (vertex p)
    vertexStar isOpen_vertexStar vertexStar_isConvex exists_mem_vertexStar γ

/-- The actual open connector-convex subsets, used only as a covering index set. -/
abbrev LoopConvexOpenSets (p : P) :=
  {W : Set (Path (vertex p) (vertex p)) // IsOpen W ∧ (loopEquiconnection p).IsConvex W}

/-- This explicit family covers the original metric based loop space. -/
theorem loopConvexOpenSets_covers (p : P) (γ : Path (vertex p) (vertex p)) :
    ∃ W : LoopConvexOpenSets p, γ ∈ W.1 := by
  obtain ⟨W, hW, hγ, hconvex⟩ := exists_convex_open_loop_neighborhood p γ
  exact ⟨⟨W, hW, hconvex⟩, hγ⟩

end Topology.MetricOrderComplex
