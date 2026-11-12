/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Tactic.Linarith

/-!
# A positive Lipschitz radius for an arbitrary metric open cover

Take the supremum of all radii at most one whose ball is contained in some
cover member. Nonpositive radii are deliberately allowed: subtracting a distance
then preserves admissibility without a positivity case split. At each actual
point the cover supplies an index for radius zero, while openness supplies a
positive admissible radius. No global nonempty-space or nonempty-index instance
is needed, and a cover member equal to the whole space causes no exception.

The half-radius ball lies in a genuine cover member by supremum approximation.
The radius itself need not be attained by any cover member.
-/

open Topology

/-! Implementation source: `Quillen/Topology/MetricSpace/CoverRadius.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps and proofs are retained. -/

@[expose] public section
noncomputable section

namespace Topology.MetricCoverRadius

variable {A κ : Type*} [PseudoMetricSpace A]

/-- All real radii bounded by one whose ball lies in an actual cover member. -/
def admissibleRadii (V : κ → Set A) (x : A) : Set ℝ :=
  {t | t ≤ 1 ∧ ∃ k, Metric.ball x t ⊆ V k}

/-- The bounded supremum radius; its geometric properties follow from coverage and openness. -/
def radius (V : κ → Set A) (x : A) : ℝ := sSup (admissibleRadii V x)

/-- The admissible radii are bounded above independently of any cover hypothesis. -/
private theorem admissibleRadii_bddAbove (V : κ → Set A) (x : A) :
    BddAbove (admissibleRadii V x) :=
  ⟨1, fun _ ht ↦ ht.1⟩

/-- At an actual covered point, radius zero is admissible because its ball is empty. -/
private theorem zero_mem_admissibleRadii (V : κ → Set A)
    (hcover : ∀ x, ∃ k, x ∈ V k) (x : A) :
    (0 : ℝ) ∈ admissibleRadii V x := by
  obtain ⟨k, _⟩ := hcover x
  refine ⟨zero_le_one, k, ?_⟩
  rw [Metric.ball_zero]
  exact Set.empty_subset (V k)

/-- Coverage supplies nonempty admissible sets pointwise, even for an empty ambient space. -/
private theorem admissibleRadii_nonempty (V : κ → Set A)
    (hcover : ∀ x, ∃ k, x ∈ V k) (x : A) :
    (admissibleRadii V x).Nonempty :=
  ⟨0, zero_mem_admissibleRadii V hcover x⟩

/-- The constructed radius is nonnegative for any cover, without openness. -/
theorem radius_nonneg (V : κ → Set A) (hcover : ∀ x, ∃ k, x ∈ V k) (x : A) :
    0 ≤ radius V x :=
  le_csSup (admissibleRadii_bddAbove V x) (zero_mem_admissibleRadii V hcover x)

/-- The constructed radius is bounded by one. -/
theorem radius_le_one (V : κ → Set A) (hcover : ∀ x, ∃ k, x ∈ V k) (x : A) :
    radius V x ≤ 1 :=
  csSup_le (admissibleRadii_nonempty V hcover x) (fun _ ht ↦ ht.1)

/-- Openness supplies a strictly positive admissible radius at every covered point. -/
theorem radius_pos (V : κ → Set A) (hopen : ∀ k, IsOpen (V k))
    (hcover : ∀ x, ∃ k, x ∈ V k) (x : A) : 0 < radius V x := by
  obtain ⟨k, hx⟩ := hcover x
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (hopen k) x hx
  have hmem : min ε 1 ∈ admissibleRadii V x :=
    ⟨min_le_right ε 1, k, (Metric.ball_subset_ball (min_le_left ε 1)).trans hball⟩
  exact (lt_min hε zero_lt_one).trans_le (le_csSup (admissibleRadii_bddAbove V x) hmem)

/-- Moving the center subtracts only its distance, including for nonpositive shifted radii. -/
private theorem sub_dist_mem_admissibleRadii (V : κ → Set A) (x y : A) {t : ℝ}
    (ht : t ∈ admissibleRadii V x) : t - dist x y ∈ admissibleRadii V y := by
  obtain ⟨ht, k, hball⟩ := ht
  refine ⟨?_, k, fun z hz ↦ hball ?_⟩
  · have hd : 0 ≤ dist x y := dist_nonneg
    linarith
  · change dist z x < t
    change dist z y < t - dist x y at hz
    have htriangle : dist z x ≤ dist z y + dist x y := by
      simpa only [dist_comm y x] using dist_triangle z y x
    linarith

/-- The radius changes by at most the distance between the two actual centers. -/
theorem radius_le_add_dist (V : κ → Set A) (hcover : ∀ x, ∃ k, x ∈ V k)
    (x y : A) : radius V x ≤ radius V y + dist x y := by
  change sSup (admissibleRadii V x) ≤ radius V y + dist x y
  apply csSup_le (admissibleRadii_nonempty V hcover x)
  intro t ht
  have hle := le_csSup (admissibleRadii_bddAbove V y)
    (sub_dist_mem_admissibleRadii V x y ht)
  change t - dist x y ≤ radius V y at hle
  linarith

/-- The radius is genuinely one-Lipschitz in the original pseudometric topology. -/
theorem lipschitz_radius (V : κ → Set A) (hcover : ∀ x, ∃ k, x ∈ V k) :
    LipschitzWith 1 (radius V) :=
  LipschitzWith.of_le_add (radius_le_add_dist V hcover)

/-- Half of the positive supremum radius has an actual containing cover member. -/
theorem half_radius_subordinate (V : κ → Set A) (hopen : ∀ k, IsOpen (V k))
    (hcover : ∀ x, ∃ k, x ∈ V k) (x : A) :
    ∃ k, Metric.ball x (radius V x / 2) ⊆ V k := by
  have hhalf : radius V x / 2 < radius V x := by
    have hpos := radius_pos V hopen hcover x
    linarith
  obtain ⟨t, ht, hlt⟩ :=
    exists_lt_of_lt_csSup (admissibleRadii_nonempty V hcover x) hhalf
  obtain ⟨_, k, hk⟩ := ht
  exact ⟨k, (Metric.ball_subset_ball hlt.le).trans hk⟩

/-- Every open metric cover supplies the exact positive Lipschitz radius needed for point-stars. -/
theorem exists_positive_lipschitz_radius (V : κ → Set A) (hopen : ∀ k, IsOpen (V k))
    (hcover : ∀ x, ∃ k, x ∈ V k) :
    ∃ r : A → ℝ, (∀ x, 0 < r x) ∧ LipschitzWith 1 r ∧
      ∀ x, ∃ k, Metric.ball x (r x / 2) ⊆ V k :=
  ⟨radius V, radius_pos V hopen hcover, lipschitz_radius V hcover,
    half_radius_subordinate V hopen hcover⟩

end Topology.MetricCoverRadius
