/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Topology.Path
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# The sup metric on the original Path topology

The forgetful map from Path x y to C(I,X) is an embedding by the original
induced compact-open definition. Pulling back the compact-domain sup metric
with IsEmbedding.comapMetricSpace preserves that existing topology explicitly.
No replacement path carrier or replacement topology is used.
-/

open Topology

/-! Implementation source: `Quillen/Topology/PathSpace/Metric.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps and proofs are retained. -/

@[expose] public section
noncomputable section

open scoped Topology unitInterval

universe u
namespace Topology.PathSpace

section Topological

variable {X : Type u} [TopologicalSpace X] {x y : X}

/-- The original Path topology is exactly induced by the forgetful map. -/
theorem isEmbedding_toContinuousMap :
    Topology.IsEmbedding (fun γ : Path x y ↦ γ.toContinuousMap) := by
  refine ⟨⟨rfl⟩, ?_⟩
  intro γ δ h
  apply Path.ext
  exact congrArg (fun f : C(I, X) ↦ (f : I → X)) h

/-- The actual forgetful map from the compact-open Path space is continuous. -/
@[fun_prop]
theorem continuous_toContinuousMap :
    Continuous (fun γ : Path x y ↦ γ.toContinuousMap) :=
  isEmbedding_toContinuousMap.continuous

end Topological

section Metric

variable {X : Type u} [MetricSpace X] {x y : X}

/-- The sup metric pulled back while retaining the original Path topology. -/
instance instMetricSpace : MetricSpace (Path x y) :=
  isEmbedding_toContinuousMap.comapMetricSpace (fun γ : Path x y ↦ γ.toContinuousMap)

/-- The inherited topology is definitionally the unchanged original compact-open Path topology. -/
theorem metricSpace_topology :
    (instMetricSpace (x := x) (y := y)).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
      Path.instTopologicalSpace := rfl

/-- The distance is exactly the sup metric of the original underlying continuous maps. -/
theorem dist_eq (γ δ : Path x y) : dist γ δ = dist γ.toContinuousMap δ.toContinuousMap := rfl

/-- Strict sup distance is detected at every time on the compact interval. -/
theorem dist_lt_iff (γ δ : Path x y) (r : ℝ) :
    dist γ δ < r ↔ ∀ t : I, dist (γ t) (δ t) < r :=
  ContinuousMap.dist_lt_iff_of_nonempty

/-- Each pointwise distance is bounded by the actual path-space sup distance. -/
theorem dist_apply_le (γ δ : Path x y) (t : I) : dist (γ t) (δ t) ≤ dist γ δ :=
  ContinuousMap.dist_apply_le_dist t

end Metric
end Topology.PathSpace
