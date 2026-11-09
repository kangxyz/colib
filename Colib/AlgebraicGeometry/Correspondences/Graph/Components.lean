/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.InvertibleChernCapComponent

/-!
# The actual graph and its component prime cycles

The source-first graph is the literal native `pullback.lift (𝟙 X) φ`.
Each generic point of the source gives an admissible native prime cycle of its
actual image point. A finite set of source generic points gives the graph
correspondence by summing those native prime cycles. The empty sum is allowed.
No connectedness, nonemptiness, source integrality, perfect-field assumption,
or chosen substitute for the native integral support is introduced.

Source provenance: `motivic_source_a6805c4`, revision
`a6805c4a87cdfd7717dd7a94039246a167f15380`, correspondence graph construction.
Mathematical reference: MVW (2006), Lecture 1, Example 1.2, printed p. 3,
including the sum of graph components for a disconnected source.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Function.locallyFinsuppWithin

attribute [local instance] Classical.propDecidable

universe u

namespace Stacks.Chow

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
  (φ : X ⟶ Y) (hφ : φ ≫ g = f)

/-- The actual source-first graph map, with its specified base compatibility. -/
def correspondenceGraphMap : X ⟶ pullback f g :=
  pullback.lift (𝟙 X) φ (by simpa using hφ.symm)

/-- The graph's actual first projection is the identity. -/
@[reassoc (attr := simp)]
theorem correspondenceGraphMap_fst :
    correspondenceGraphMap f g φ hφ ≫ pullback.fst f g = 𝟙 X := by
  simp [correspondenceGraphMap]

/-- The graph's actual second projection is the original morphism. -/
@[reassoc (attr := simp)]
theorem correspondenceGraphMap_snd :
    correspondenceGraphMap f g φ hφ ≫ pullback.snd f g = φ := by
  simp [correspondenceGraphMap]

/-- Separatedness of the target makes the literal graph a closed immersion. -/
theorem isClosedImmersion_correspondenceGraphMap [IsSeparated g] :
    IsClosedImmersion (correspondenceGraphMap f g φ hφ) := by
  have : IsClosedImmersion (correspondenceGraphMap f g φ hφ ≫ pullback.fst f g) := by
    rw [correspondenceGraphMap_fst]
    infer_instance
  exact IsClosedImmersion.of_comp _ (pullback.fst f g)

/-- Every actual source generic point gives a finite admissible graph component. -/
theorem isFiniteCorrespondencePoint_graphMap [IsSeparated g] (t : genericPoints X) :
    IsFiniteCorrespondencePoint f g (correspondenceGraphMap f g φ hφ t.val) := by
  let j := correspondenceGraphMap f g φ hφ
  let : IsClosedImmersion j := isClosedImmersion_correspondenceGraphMap f g φ hφ
  obtain ⟨e, he⟩ := Stacks.Chow.exists_iso_integralComponentAt_comp j t.val
  have hf : e.hom ≫ (integralComponentAt (j t.val)).subschemeι ≫ pullback.fst f g =
      (integralComponentAt t.val).subschemeι := by
    simpa only [Category.assoc, j, correspondenceGraphMap_fst, Category.comp_id] using
      congrArg (fun k => k ≫ pullback.fst f g) he
  have hπ : (integralComponentAt (j t.val)).subschemeι ≫ pullback.fst f g =
      e.inv ≫ (integralComponentAt t.val).subschemeι := by
    apply (cancel_epi e.hom).mp
    simpa only [Iso.hom_inv_id_assoc] using hf
  have hfin : IsFinite ((integralComponentAt (j t.val)).subschemeι ≫ pullback.fst f g) := by
    rw [hπ]
    infer_instance
  refine ⟨hfin, ?_⟩
  have hr := range_eq_range_of_surjective (integralComponentAt t.val).subschemeι
    ((integralComponentAt (j t.val)).subschemeι ≫ pullback.fst f g) e.hom hf
  rw [← hr, Scheme.IdealSheafData.range_subschemeι, coe_support_integralComponentAt]
  exact t.property

/-- The graph correspondence is a finite sum of native graph-component prime cycles. -/
def graphCorrespondenceOfComponents [IsSeparated g] (hX : (genericPoints X).Finite) :
    finiteCorrespondences f g := by
  classical
  refine ⟨∑ t ∈ hX.toFinset, single (correspondenceGraphMap f g φ hφ t) 1, ?_⟩
  apply AddSubgroup.sum_mem
  intro t ht
  exact single_mem_finiteCorrespondences f g _
    (isFiniteCorrespondencePoint_graphMap f g φ hφ ⟨t, hX.mem_toFinset.mp ht⟩) 1

/-- The graph sum retains its literal native prime cycles and coefficient one. -/
theorem graphCorrespondenceOfComponents_coe [IsSeparated g] (hX : (genericPoints X).Finite) :
    (graphCorrespondenceOfComponents f g φ hφ hX).1 =
      ∑ t ∈ hX.toFinset, single (correspondenceGraphMap f g φ hφ t) 1 := rfl

/-- Empty sources contribute the zero graph correspondence. -/
theorem graphCorrespondenceOfComponents_eq_zero_of_isEmpty [IsSeparated g] [IsEmpty X]
    (hX : (genericPoints X).Finite) : graphCorrespondenceOfComponents f g φ hφ hX = 0 := by
  apply Subtype.ext
  change (∑ t ∈ hX.toFinset, single (correspondenceGraphMap f g φ hφ t) 1) = 0
  have : hX.toFinset = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x
    exact isEmptyElim x
  rw [this]
  simp

end Stacks.Chow
