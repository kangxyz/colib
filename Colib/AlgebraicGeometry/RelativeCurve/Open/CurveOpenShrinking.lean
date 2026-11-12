/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.Topology.Dimension.DimensionLEOne
public import Mathlib.AlgebraicGeometry.Artinian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Shrinking a curve without losing a specified closed complement

On a Noetherian curve, an open containing every component generic point misses
only finitely many closed points. Inside an open of a Jacobson scheme, these
points remain closed in the ambient scheme. Removing precisely those points
shrinks the overlap while retaining the complete original closed complement.
No perfectness or separability hypothesis on closed residue fields is used.
-/

/-!
Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Aglib/AlgebraicGeometry/RelativeCurve/Open/CurveOpenShrinking.lean`, blob
`2a88f59a7064d91eab77a44278ae540904ab347f`.
Only the actual generic fiber receives a curve-dimension bound. The original
total space, overlap and full finite boundary are retained. Ordinary cohomology
uses the native free-Yoneda Ext source.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- The entire complement of an open containing every component generic point
in a Noetherian scheme of dimension at most one is finite and consists of
closed points. The scheme may be empty or disconnected. -/
theorem finite_closed_complement_of_genericPoints_subset
    {X : Scheme.{u}} [IsNoetherian X] (O : X.Opens)
    (hgeneric : genericPoints X ⊆ (O : Set X))
    (hdim : topologicalKrullDim X ≤ 1) :
    ((O : Set X)ᶜ).Finite ∧ ∀ x : X, x ∉ O → IsClosed ({x} : Set X) := by
  have hcomponent : ∀ C ∈ irreducibleComponents X, ¬ C ⊆ (O : Set X)ᶜ := by
    intro C hC hsub
    let x := genericPoints.ofComponent (⟨C, hC⟩ : irreducibleComponents X)
    exact hsub (genericPoints.isGenericPoint_ofComponent
      (⟨C, hC⟩ : irreducibleComponents X)).mem (hgeneric x.property)
  refine ⟨Stacks.Topology.Dimension.finite_of_not_irreducibleComponent_subset
    hdim O.isOpen.isClosed_compl hcomponent, ?_⟩
  intro x hx
  exact Stacks.Topology.Dimension.isClosed_singleton_of_not_irreducibleComponent_subset
    hdim O.isOpen.isClosed_compl hcomponent hx


/-- A dense-on-every-component open inside an open curve can be realized as
its intersection with an ambient open retaining the entire old complement.
The finiteness and closedness of the removed set are conclusions. -/
theorem exists_open_shrinking_retaining_complement
    {V : Scheme.{u}} [IsNoetherian V] [JacobsonSpace V]
    (W : V.Opens) (O : W.toScheme.Opens)
    (hgeneric : genericPoints W.toScheme ⊆ (O : Set W.toScheme))
    (hdim : topologicalKrullDim W.toScheme ≤ 1) :
    ∃ T : V.Opens, (W : Set V)ᶜ ⊆ (T : Set V) ∧
      W.ι ⁻¹ᵁ T = O ∧ ((T : Set V)ᶜ).Finite := by
  let : IsLocallyNoetherian W.toScheme := LocallyOfFiniteType.isLocallyNoetherian W.ι
  let : NoetherianSpace W.toScheme :=
    W.ι.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  let : IsNoetherian W.toScheme := ⟨⟩
  obtain ⟨hfinite, hclosed⟩ :=
    finite_closed_complement_of_genericPoints_subset O hgeneric hdim
  let E : Set V := W.ι '' (O : Set W.toScheme)ᶜ
  have hEfinite : E.Finite := hfinite.image W.ι
  have hEclosed : IsClosed E := by
    rw [show E = ⋃ x ∈ E, ({x} : Set V) by simp]
    apply hEfinite.isClosed_biUnion
    rintro x ⟨y, hy, rfl⟩
    exact W.ι.closedPoints_subset_preimage_closedPoints (hclosed y hy)
  let T : V.Opens := ⟨Eᶜ, hEclosed.isOpen_compl⟩
  refine ⟨T, ?_, ?_, ?_⟩
  · rintro x hx ⟨y, _, rfl⟩
    exact hx y.property
  · ext x
    change W.ι x ∉ E ↔ x ∈ O
    simp only [E, Set.mem_image, Set.mem_compl_iff]
    constructor
    · intro hx
      by_contra hn
      exact hx ⟨x, hn, rfl⟩
    · rintro hx ⟨y, hy, he⟩
      exact hy (W.ι.isOpenEmbedding.injective he ▸ hx)
  · simpa only [T, Opens.coe_mk, compl_compl] using hEfinite

end AlgebraicGeometry.Scheme
