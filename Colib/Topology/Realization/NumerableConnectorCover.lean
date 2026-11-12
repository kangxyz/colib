/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalEquiconnection
public import Mathlib.Topology.PartitionOfUnity
public import Mathlib.Geometry.Convex.ConvexSpace.Topology

/-!
# Point-star carriers and genuine finite partition charts

A point-star refinement is enough for Milnor's nerve construction. It is not
an ordinary refinement. Closed-support subordination, rather than merely
local finiteness, supplies a single nerve simplex containing all nearby
partition supports. No map into a weak realization is asserted from
coordinatewise continuity alone.
-/

open Topology

/-! Implementation source: `Quillen/Topology/Realization/NumerableConnectorCover.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps and proofs are retained. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Filter Set Convexity
open scoped Topology
universe u v w
namespace Topology.NumerableConnectorCover
variable {A : Type u} {ι : Type v} {κ : Type w}

/-- The union of all cover members which contain a given point. -/
def pointStar (W : ι → Set A) (x : A) : Set A :=
  {y | ∃ i, x ∈ W i ∧ y ∈ W i}

/-- Every point-star lies in one member of the target cover. -/
def PointStarRefines (W : ι → Set A) (V : κ → Set A) : Prop :=
  ∀ x, ∃ k, pointStar W x ⊆ V k

/-- The finite intersection condition defining the (unordered) nerve faces. -/
def IsNerveFace (W : ι → Set A) (s : Finset ι) : Prop :=
  ∃ x, ∀ i ∈ s, x ∈ W i

/-- Nerve faces are closed under taking finite subsets. -/
theorem IsNerveFace.mono {W : ι → Set A} {s t : Finset ι}
    (ht : IsNerveFace W t) (hst : s ⊆ t) : IsNerveFace W s := by
  obtain ⟨x, hx⟩ := ht
  exact ⟨x, fun i hi ↦ hx i (hst hi)⟩

/-- A point-star carrier contains both its witnessing point and all selected vertices. -/
theorem pointStar_carrier (W : ι → Set A) (V : κ → Set A)
    (hcover : ∀ x, ∃ i, x ∈ W i) (href : PointStarRefines W V)
    (vertex : ι → A) (hvertex : ∀ i, vertex i ∈ W i) (x : A) :
    ∃ k, x ∈ V k ∧ ∀ i, x ∈ W i → vertex i ∈ V k := by
  obtain ⟨k, hk⟩ := href x
  obtain ⟨i, hi⟩ := hcover x
  exact ⟨k, hk ⟨i, hi, hi⟩, fun j hj ↦ hk ⟨j, hj, hvertex j⟩⟩

variable [TopologicalSpace A]

/-- A subordinate partition has a single genuine nerve simplex controlling a neighborhood. -/
theorem localNerveFace (ρ : PartitionOfUnity ι A) {W : ι → Set A}
    (hρ : ρ.IsSubordinate W) (x : A) :
    IsNerveFace W (ρ.fintsupport x) ∧
      ∀ᶠ y in 𝓝 x, ρ.finsupport y ⊆ ρ.fintsupport x := by
  refine ⟨⟨x, ?_⟩, ρ.eventually_finsupport_subset x⟩
  intro i hi
  exact hρ i ((ρ.mem_fintsupport_iff x i).mp hi)

/-- The locus on which a fixed finite set contains all positive partition coordinates. -/
def chartDomain (ρ : PartitionOfUnity ι A) (s : Finset ι) : Set A :=
  {x | ρ.finsupport x ⊆ s}

/-- The canonical closed-support chart domain really is a neighborhood. -/
theorem chartDomain_mem_nhds (ρ : PartitionOfUnity ι A) (x : A) :
    chartDomain ρ (ρ.fintsupport x) ∈ 𝓝 x :=
  ρ.eventually_finsupport_subset x

/-- Actual finite barycentric coordinates on one fixed support chart. -/
def finiteChart (ρ : PartitionOfUnity ι A) (s : Finset ι) :
    C(chartDomain ρ s, StdSimplex ℝ s) where
  toFun x := {
    weights := Finsupp.equivFunOnFinite.symm (fun i ↦ ρ i.1 x.1)
    nonneg i := ρ.nonneg i.1 x.1
    total := by
      rw [Finsupp.sum_fintype _ _ (by simp)]
      change (∑ i : s, ρ i.1 x.1) = 1
      exact (Finset.sum_coe_sort s (fun i : ι ↦ ρ i x.1)).trans
        (ρ.sum_finsupport' (mem_univ x.1) x.2) }
  continuous_toFun := by
    rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ s).continuous_iff]
    refine continuous_pi fun i ↦ ?_
    exact (ρ i.1).continuous.comp continuous_subtype_val

/-- The finite chart retains the original partition coefficients literally. -/
@[simp] theorem finiteChart_weights (ρ : PartitionOfUnity ι A) (s : Finset ι)
    (x : chartDomain ρ s) (i : s) : (finiteChart ρ s x).weights i = ρ i.1 x.1 := rfl

/-- Each finite nerve face has a common connector-convex carrier for its chosen vertices. -/
theorem nerveFace_convexCarrier (E : LocalEquiconnection A)
    (W : ι → Set A) (V : κ → Set A) (hconvex : ∀ k, E.IsConvex (V k))
    (href : PointStarRefines W V) (vertex : ι → A) (hvertex : ∀ i, vertex i ∈ W i)
    {s : Finset ι} (hs : IsNerveFace W s) :
    ∃ k, E.IsConvex (V k) ∧ ∀ i ∈ s, vertex i ∈ V k := by
  obtain ⟨x, hx⟩ := hs
  obtain ⟨k, hk⟩ := href x
  exact ⟨k, hconvex k, fun i hi ↦ hk ⟨i, hx i hi, hvertex i⟩⟩

end Topology.NumerableConnectorCover
