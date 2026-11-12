/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Realization.NumerableRealizationDomination
public import Colib.Topology.MetricSpace.CoverRadius
public import Colib.Topology.Realization.MetricPointStarRefinement
public import Mathlib.Topology.EMetricSpace.Paracompact

/-!
# Actual metric-space realization domination from local convex geometry

The radius is the separately proved supremum construction. Its one-eighth
balls form an actual point-star refinement, with their centers as selected
vertices. Pinned metric paracompactness gives an actual subordinate partition
of unity. A classical order on the indexing set merely orders the nerve;
it imposes no order-topology hypothesis on the original metric space.
-/

open SSet Topology CategoryTheory

/-! Implementation source: `Quillen/Topology/Realization/MetricRealizationDomination.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps and proofs are retained. -/

@[expose] public section
noncomputable section
open Convexity CategoryTheory Opposite
open scoped Topology Simplicial
universe u w
namespace Topology.NumerableConnectorCover
variable {A : Type u} [MetricSpace A] {κ : Type w}

/-- A metric space with a continuous local connector and an open connector-convex cover
is genuinely dominated by a constructed simplicial-set realization. -/
theorem exists_metric_realization_domination (E : LocalEquiconnection A)
    (V : κ → Set A) (hopen : ∀ k, IsOpen (V k)) (hconvex : ∀ k, E.IsConvex (V k))
    (hcover : ∀ x, ∃ k, x ∈ V k) :
    ∃ (K : SSet.{u}) (a : C(A, |K|)) (b : C(|K|, A)),
      Nonempty ((b.comp a).Homotopy (ContinuousMap.id A)) := by
  let : LinearOrder A := IsWellOrder.linearOrder (@WellOrderingRel A)
  obtain ⟨r, hpos, hLip, hsmall⟩ :=
    MetricCoverRadius.exists_positive_lipschitz_radius V hopen hcover
  let W : A → Set A := fun x ↦ Metric.ball x (r x / 8)
  have hcenter : ∀ x, x ∈ W x := by
    intro x
    change dist x x < r x / 8
    simpa only [dist_self] using div_pos (hpos x) (by norm_num : (0 : ℝ) < 8)
  have hWcover : ∀ x, ∃ y, x ∈ W y := fun x ↦ ⟨x, hcenter x⟩
  have href : PointStarRefines W V := pointStarRefines_radius V r hpos hLip hsmall
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ W
    (fun _ ↦ Metric.isOpen_ball) (by
      intro x _
      exact Set.mem_iUnion.mpr (hWcover x))
  exact exists_numerable_realization_domination E W V hconvex href hWcover id hcenter ρ hρ

end Topology.NumerableConnectorCover
