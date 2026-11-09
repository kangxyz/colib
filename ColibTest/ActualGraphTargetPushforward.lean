/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Graph.TargetPushforward

/-! Native consumer checks for actual target pushforward and graph cancellation.
 -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace AlgebraicGeometry.Cor

variable (k : Type u) [Field k]
  {X Y Z : Scheme.SmoothSite (Spec (.of k))} (q : Y ⟶ Z)

example [IsFinite (graphTargetMap k X q)] (α β : Cor.mk X ⟶ Cor.mk Y) :
    ((α - β) ≫ (graphFunctor k).map q).val =
      finiteCyclePushforward (graphTargetMap k X q) (α - β).val :=
  comp_graph_val_of_finite k q (α - β)

example [IsClosedImmersion q.left] : Mono ((graphFunctor k).map q) := inferInstance

example [IsClosedImmersion q.left] (α β : Cor.mk X ⟶ Cor.mk Y)
    (h : α ≫ (graphFunctor k).map q = β ≫ (graphFunctor k).map q) : α = β :=
  (cancel_mono ((graphFunctor k).map q)).mp h

example [IsFinite (graphTargetMap k X q)] (α : Cor.mk X ⟶ Cor.mk Y)
    (y : ↥(pullback X.hom Z.hom)) :
    (α ≫ (graphFunctor k).map q).val y =
      ∑ᶠ x ∈ (graphTargetMap k X q).base ⁻¹' {y},
        α.val x * ((graphTargetMap k X q).residueDegree x : ℤ) := by
  rw [comp_graph_val_of_finite]
  exact finiteCyclePushforward_apply _ _ _

end AlgebraicGeometry.Cor
