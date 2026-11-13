/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Realization.POUNerveClassifier
public import Colib.Topology.Realization.OrderedNerveRealizationMap

/-!
# Constructed numerable domination by an actual cover-nerve realization

Both maps are the actual constructions from original partition coefficients
and ordered convex interpolation. Point-star control supplies a common
carrier for each point and the returned value. The original connector then
constructs the composite homotopy. No map, homotopy, or domination certificate
is part of the hypotheses.
-/

open SSet Topology CategoryTheory

/-! Implementation source: `Quillen/Topology/Realization/NumerableRealizationDomination.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps and proofs are retained. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Convexity CategoryTheory Opposite
open scoped Topology Simplicial
universe u v w
namespace Topology.NumerableConnectorCover
variable {A : Type u} [TopologicalSpace A] {ι : Type v} [LinearOrder ι] {κ : Type w}
variable (E : LocalEquiconnection A) (W : ι → Set A) (V : κ → Set A)
variable (hconvex : ∀ k, E.IsConvex (V k)) (href : PointStarRefines W V)
variable (hcover : ∀ x, ∃ i, x ∈ W i) (vertex : ι → A) (hvertex : ∀ i, vertex i ∈ W i)
variable (ρ : PartitionOfUnity ι A) (hρ : ρ.IsSubordinate W)

include hcover in
/-- The original point and the actual returned partition value have one common convex carrier. -/
theorem partition_return_carrier (x : A) :
    ∃ k, x ∈ V k ∧
      nerveReturnMap E W V hconvex href vertex hvertex (partitionNerveMap W ρ hρ x) ∈ V k := by
  obtain ⟨k, hx, hv⟩ := pointStar_carrier W V hcover href vertex hvertex x
  refine ⟨k, hx, ?_⟩
  rw [partitionNerveMap_apply]
  let s := ρ.finsupport x
  let hs := partition_finsupport_nonempty ρ x
  let hf := partition_support_isNerveFace W ρ hρ x
  change nerveReturnMap E W V hconvex href vertex hvertex
    (realizationSimplex (finiteFaceSimplex W s hs hf)
      ((finiteChart ρ s ⟨x, Finset.Subset.refl _⟩).map
        (s.orderIsoOfFin (finiteFace_card s hs)).symm)) ∈ V k
  apply nerveReturnMap_mem E W V hconvex href vertex hvertex
    (SSet.S.mk (finiteFaceSimplex W s hs hf)) _ (hconvex k)
  intro i
  apply hv
  apply hρ
  apply (ρ.mem_fintsupport_iff x _).mp
  apply ρ.finsupport_subset_fintsupport x
  exact s.orderEmbOfFin_mem _ i

/-- The actual connector homotopy from the constructed return/classifier composite to identity. -/
def numerableDominationHomotopy :
    ((nerveReturnMap E W V hconvex href vertex hvertex).comp
      (partitionNerveMap W ρ hρ)).Homotopy (ContinuousMap.id A) :=
  E.carrierHomotopy _ _ fun x ↦ by
    obtain ⟨k, hx, hb⟩ := partition_return_carrier E W V hconvex href hcover vertex hvertex ρ hρ x
    exact ⟨V k, hconvex k, hb, hx⟩

include E W V hconvex href hcover vertex hvertex ρ hρ in
/-- A subordinate original partition and point-star geometric data produce actual realization
domination. The simplicial set, both continuous maps, and their homotopy are constructed. -/
theorem exists_numerable_realization_domination :
    ∃ (K : SSet.{v}) (a : C(A, |K|)) (b : C(|K|, A)),
      Nonempty ((b.comp a).Homotopy (ContinuousMap.id A)) :=
  ⟨(orderedNerve W).toSSet, partitionNerveMap W ρ hρ,
    nerveReturnMap E W V hconvex href vertex hvertex,
    ⟨numerableDominationHomotopy E W V hconvex href hcover vertex hvertex ρ hρ⟩⟩

end Topology.NumerableConnectorCover
