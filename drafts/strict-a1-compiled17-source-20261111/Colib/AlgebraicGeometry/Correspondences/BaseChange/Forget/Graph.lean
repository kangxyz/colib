/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.BaseChange.Forget.Cycle
public import Colib.AlgebraicGeometry.Correspondences.Graph.Components

/-!
# Actual graphs after forgetting the base

Closed-immersion pushforward preserves the coefficient one at each original
generic source point. Thus it preserves the full graph, including disconnected
or empty sources, rather than just the graph of an integral source.

Adapted from `Motivic/AlgebraicGeometry/Correspondences/BaseChange/Forget/Graph.lean`
at `a6805c4a87cdfd7717dd7a94039246a167f15380`, blob
`73a0d71a0f7f19fa8c03fb4dd6799ff9b31214af`, on native cycle groups.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme
open Function.locallyFinsuppWithin
open scoped BigOperators

universe u

namespace Stacks.Chow

variable {S T X Y : Scheme.{u}} (r : T ⟶ S) (f : X ⟶ T) (g : Y ⟶ T)
  (φ : X ⟶ Y) (hφ : φ ≫ g = f)

/-- The source-first graph retains both literal projections after forgetting. -/
@[reassoc]
theorem correspondenceGraphMap_forgetBase :
    correspondenceGraphMap f g φ hφ ≫ forgetBaseProductMap r f g =
      correspondenceGraphMap (f ≫ r) (g ≫ r) φ (by rw [← Category.assoc, hφ]) := by
  apply pullback.hom_ext <;> simp only [Category.assoc,
    forgetBaseProductMap_fst, forgetBaseProductMap_snd,
    correspondenceGraphMap_fst, correspondenceGraphMap_snd]

variable [IsSeparated r] [LocallyOfFiniteType r] [IsSeparated g] [LocallyOfFiniteType g]

/-- Native finite pushforward preserves the whole componentwise graph cycle. -/
theorem finiteCorrespondencesForgetBase_graph (hX : (genericPoints X).Finite) :
    finiteCorrespondencesForgetBase r f g
        (graphCorrespondenceOfComponents f g φ hφ hX) =
      graphCorrespondenceOfComponents (f ≫ r) (g ≫ r) φ
        (by rw [← Category.assoc, hφ]) hX := by
  apply Subtype.ext
  simp only [finiteCorrespondencesForgetBase_val, graphCorrespondenceOfComponents_coe,
    map_sum, finiteCyclePushforward_single_of_isClosedImmersion,
    ← Scheme.Hom.comp_apply, correspondenceGraphMap_forgetBase]

end Stacks.Chow
