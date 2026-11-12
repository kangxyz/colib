/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Realization.FiniteNerveCharts

/-!
# The actual partition-of-unity map into the weak cover-nerve realization

The value uses exactly the original positive partition coefficients. Around
every point a single finite CLOSED support set controls all nearby values.
Exact finite-chart inclusion identities prove local chart factorization, hence
continuity into the weak realization. Coordinatewise continuity is not used
as a substitute for the weak-topology argument.
-/

open SSet Topology CategoryTheory

/-! Implementation source: `Quillen/Topology/Realization/POUNerveClassifier.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps and proofs are retained. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Convexity CategoryTheory Opposite
open scoped Topology Simplicial
universe u v
namespace Topology.NumerableConnectorCover
variable {A : Type u} [TopologicalSpace A] {ι : Type v} [LinearOrder ι]
variable (W : ι → Set A) (ρ : PartitionOfUnity ι A) (hρ : ρ.IsSubordinate W)

omit [LinearOrder ι] in
include hρ in
/-- The original nonzero partition support is an actual common-intersection nerve face. -/
theorem partition_support_isNerveFace (x : A) : IsNerveFace W (ρ.finsupport x) :=
  ((localNerveFace ρ hρ x).1).mono (ρ.finsupport_subset_fintsupport x)

/-- The classifier's actual pointwise value, using precisely the original partition weights. -/
def partitionNerveValue (x : A) : |(orderedNerve W).toSSet| :=
  finiteNerveChart W (ρ.finsupport x) (partition_finsupport_nonempty ρ x)
    (partition_support_isNerveFace W ρ hρ x)
    (finiteChart ρ (ρ.finsupport x) ⟨x, Finset.Subset.refl _⟩)

/-- Any finite nerve face containing the positive support gives exactly the same point. -/
theorem partitionNerveValue_eq_chart (s : Finset ι) (hs : s.Nonempty)
    (hface : IsNerveFace W s) (x : chartDomain ρ s) :
    partitionNerveValue W ρ hρ x.1 = finiteNerveChart W s hs hface (finiteChart ρ s x) := by
  let t := ρ.finsupport x.1
  let ht := partition_finsupport_nonempty ρ x.1
  let htface := partition_support_isNerveFace W ρ hρ x.1
  let y : chartDomain ρ t := ⟨x.1, Finset.Subset.refl _⟩
  change finiteNerveChart W t ht htface (finiteChart ρ t y) = _
  rw [← finiteNerveChart_inclusion W ht hs x.2 htface hface]
  rw [finiteChart_map_inclusion]

/-- On each fixed finite support domain, the actual classifier is one continuous chart. -/
theorem partitionNerveValue_continuousOn (s : Finset ι) (hs : s.Nonempty)
    (hface : IsNerveFace W s) :
    ContinuousOn (partitionNerveValue W ρ hρ) (chartDomain ρ s) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have he : (chartDomain ρ s).domRestrict (partitionNerveValue W ρ hρ) =
      fun x ↦ finiteNerveChart W s hs hface (finiteChart ρ s x) := by
    funext x
    exact partitionNerveValue_eq_chart W ρ hρ s hs hface x
  rw [he]
  exact (finiteNerveChart W s hs hface).continuous.comp (finiteChart ρ s).continuous

/-- Local closed-support control proves continuity into the original weak realization. -/
theorem continuous_partitionNerveValue : Continuous (partitionNerveValue W ρ hρ) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hs : (ρ.fintsupport x).Nonempty :=
    (partition_finsupport_nonempty ρ x).mono (ρ.finsupport_subset_fintsupport x)
  exact (partitionNerveValue_continuousOn W ρ hρ (ρ.fintsupport x) hs
    (localNerveFace ρ hρ x).1).continuousAt (chartDomain_mem_nhds ρ x)

/-- The genuine original-partition map to the weak ordered-nerve realization. -/
def partitionNerveMap : C(A, |(orderedNerve W).toSSet|) :=
  ⟨partitionNerveValue W ρ hρ, continuous_partitionNerveValue W ρ hρ⟩

/-- The classifier retains its literal original positive-support chart. -/
@[simp] theorem partitionNerveMap_apply (x : A) :
    partitionNerveMap W ρ hρ x =
      finiteNerveChart W (ρ.finsupport x) (partition_finsupport_nonempty ρ x)
        (partition_support_isNerveFace W ρ hρ x)
        (finiteChart ρ (ρ.finsupport x) ⟨x, Finset.Subset.refl _⟩) := rfl

end Topology.NumerableConnectorCover
