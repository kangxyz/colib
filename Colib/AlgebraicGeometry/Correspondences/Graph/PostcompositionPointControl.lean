/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph.PointControl

/-!
Adapted from motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Motivic/AlgebraicGeometry/Correspondences/Graph/PostcompositionPointControl.lean`,
blob `d1abcd494b8260c534901d1f4cd0e0b19e2f4ef0`.

# Actual target centers under graph postcomposition

The native graph support satisfies its literal graph equation at every point.
Signed incidence provenance therefore carries each designated center to its
actual image under the target map. Colliding graph images and cancellation
are allowed; only surviving output components require a witness.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow
open Function.locallyFinsuppWithin

universe u

namespace AlgebraicGeometry.Cor

variable (k : Type u) [Field k]
  {X Y V : Scheme.SmoothSite (Spec (.of k))}

/-- Postcomposing a signed correspondence with the actual graph carries its
designated target center to the actual image center. -/
theorem target_eq_of_comp_graph
    (α : Cor.mk X ⟶ Cor.mk Y) (q : Y ⟶ V) (x : X.left) (y : Y.left)
    (hα : ∀ a : α.property.1.toFinset, ∀ t : (integralComponentAt a.val).subscheme,
      ((integralComponentAt a.val).subschemeι ≫ pullback.fst X.hom Y.hom) t = x →
      ((integralComponentAt a.val).subschemeι ≫ pullback.snd X.hom Y.hom) t = y)
    (b : pullback (C := Scheme) X.hom V.hom)
    (hb : ((α ≫ (graphFunctor k).map q).val b) ≠ 0)
    (t : (integralComponentAt b).subscheme)
    (ht : ((integralComponentAt b).subschemeι ≫ pullback.fst X.hom V.hom) t = x) :
    ((integralComponentAt b).subschemeι ≫ pullback.snd X.hom V.hom) t = q.left y := by
  obtain ⟨z, w, a, d, hs, hm, he⟩ :=
    exists_support_points_of_incidenceTorPairing_ne_zero X.hom Y.hom V.hom
      α ((graphFunctor k).map q) b hb t
  have hw : ((graphFunctor k).map q).val w.val ≠ 0 := by
    exact ((graphFunctor k).map q).property.1.mem_toFinset.mp w.property
  have hg := graphCorrespondenceOfComponents_projection_eq Y.hom V.hom q.left
    (MorphismProperty.Over.w q) (finite_genericPoints k (Cor.mk Y)) w.val hw d
  exact he.symm.trans (hg.trans (congrArg q.left (hm.symm.trans (hα z a (hs.trans ht)))))

end AlgebraicGeometry.Cor
