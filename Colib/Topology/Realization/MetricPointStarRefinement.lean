/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Realization.NumerableConnectorCover
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Point-star control from a positive Lipschitz cover radius

This is the geometric estimate, separate from the still-required construction
of such a radius for an arbitrary open cover. The radius hypothesis does not
include a nerve map, extension, or domination witness.
-/

open Topology

/-! Implementation source: `Quillen/Topology/Realization/MetricPointStarRefinement.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps and proofs are retained. -/

@[expose] public section
noncomputable section
namespace Topology.NumerableConnectorCover
variable {A κ : Type*} [MetricSpace A]

/-- Balls of one eighth of a positive 1-Lipschitz radius form a point-star refinement. -/
theorem pointStarRefines_radius (V : κ → Set A) (r : A → ℝ)
    (hpos : ∀ x, 0 < r x) (hLip : LipschitzWith 1 r)
    (hsmall : ∀ x, ∃ k, Metric.ball x (r x / 2) ⊆ V k) :
    PointStarRefines (fun x ↦ Metric.ball x (r x / 8)) V := by
  intro x
  obtain ⟨k, hk⟩ := hsmall x
  refine ⟨k, fun z hz ↦ hk ?_⟩
  obtain ⟨y, hxy, hzy⟩ := hz
  have hxy' : dist y x < r y / 8 := by
    simpa only [Metric.mem_ball, dist_comm] using hxy
  have hzy' : dist z y < r y / 8 := hzy
  have hd : r y - r x ≤ dist y x := by
    have hl := hLip.dist_le_mul y x
    simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hl
    exact (le_abs_self _).trans hl
  have ht := dist_triangle z y x
  change dist z x < r x / 2
  nlinarith [hpos x]

/-- These radius balls cover every point, independently of the refinement estimate. -/
theorem radiusBalls_cover (r : A → ℝ) (hpos : ∀ x, 0 < r x) (x : A) :
    ∃ y, x ∈ Metric.ball y (r y / 8) := by
  refine ⟨x, ?_⟩
  simpa only [Metric.mem_ball, dist_self] using div_pos (hpos x) (by norm_num : (0 : ℝ) < 8)

end Topology.NumerableConnectorCover
