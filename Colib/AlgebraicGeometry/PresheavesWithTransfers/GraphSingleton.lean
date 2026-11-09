/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.GraphRestriction
public import Mathlib.CategoryTheory.Sites.IsSheafFor

/-!
# Actual graph restriction and disjoint-union descent

Adapted from motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Motivic/Transfers/Presheaf/NisnevichComparison.lean`, blob
`45418deb4609a06d5a1068eb2356b6c208361b42`, the independent lower comparisons.
Only the native correspondence category and the stated actual restriction maps
are used. No fullness or general continuity of the graph functor is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u v

namespace AlgebraicGeometry.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k]

/-- The ordinary singleton sheaf condition implies the corresponding condition
for actual correspondences: compatibility for all correspondences includes
compatibility for graph arrows. -/
theorem isSheafFor_graph_singleton_of_restriction
    (F : (Cor k)ᵒᵖ ⥤ Type v) {X Y : SmoothSite (Spec (.of k))} (q : Y ⟶ X)
    (hF : Presieve.IsSheafFor ((Cor.graphFunctor k).op ⋙ F) (Presieve.singleton q)) :
    Presieve.IsSheafFor F (Presieve.singleton ((Cor.graphFunctor k).map q)) := by
  rw [Presieve.isSheafFor_singleton] at hF ⊢
  intro s hs
  apply hF s
  intro Z p₁ p₂ hp
  exact hs ((Cor.graphFunctor k).map p₁) ((Cor.graphFunctor k).map p₂)
    (by simpa only [← Functor.map_comp] using congrArg ((Cor.graphFunctor k).map) hp)

end AlgebraicGeometry.PresheafWithTransfers
