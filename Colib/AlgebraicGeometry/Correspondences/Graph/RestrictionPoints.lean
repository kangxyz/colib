/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph.PointControl

/-!
# Actual support points before and after graph composition

These are pointwise provenance statements for the genuine signed native
correspondences. The witness belongs to a surviving input component; its source
and target are compared with the actual scheme maps, not with support labels.

Source locators at motivic@a6805c4a87cdfd7717dd7a94039246a167f15380:
`Motivic/AlgebraicGeometry/Correspondences/Graph/PostcompositionPointControl.lean`,
blob `d1abcd494b8260c534901d1f4cd0e0b19e2f4ef0`, and the graph-restriction use in
`Motivic/Transfers/Sheaf/Germs/Pointed/Lifts/CorrespondenceAlgebra.lean`,
blob `d809712c6c984af6081bd2e5456c5d095f630c50`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow
open Function.locallyFinsuppWithin

universe u

namespace AlgebraicGeometry.Cor

variable (k : Type u) [Field k]

/-- An actual point after signed graph restriction lifts to an actual original
support point, with exact source image and unchanged target. -/
theorem exists_support_point_of_graph_comp_ne_zero
    {U X Y : Scheme.SmoothSite (Spec (.of k))}
    (α : Cor.mk X ⟶ Cor.mk Y) (q : U ⟶ X)
    (b : pullback (C := Scheme) U.hom Y.hom)
    (hb : (((graphFunctor k).map q ≫ α).val b) ≠ 0)
    (t : (integralComponentAt b).subscheme) :
    ∃ a : α.property.1.toFinset, ∃ d : (integralComponentAt a.val).subscheme,
      ((integralComponentAt a.val).subschemeι ≫ pullback.fst X.hom Y.hom) d =
        q.left (((integralComponentAt b).subschemeι ≫ pullback.fst U.hom Y.hom) t) ∧
      ((integralComponentAt a.val).subschemeι ≫ pullback.snd X.hom Y.hom) d =
        ((integralComponentAt b).subschemeι ≫ pullback.snd U.hom Y.hom) t := by
  obtain ⟨z, w, a, d, hs, hm, he⟩ :=
    exists_support_points_of_incidenceTorPairing_ne_zero U.hom X.hom Y.hom
      ((graphFunctor k).map q) α b hb t
  have hz : ((graphFunctor k).map q).val z.val ≠ 0 := by
    exact ((graphFunctor k).map q).property.1.mem_toFinset.mp z.property
  have hg := graphCorrespondenceOfComponents_projection_eq U.hom X.hom q.left
    (MorphismProperty.Over.w q) (finite_genericPoints k (Cor.mk U)) z.val hz a
  exact ⟨w, d, hm.symm.trans (hg.trans (congrArg q.left hs)), he⟩

/-- An actual point after signed graph postcomposition comes from a genuine
input support point, with unchanged source and exact postcomposed target. -/
theorem exists_support_point_of_comp_graph_ne_zero
    {X Y V : Scheme.SmoothSite (Spec (.of k))}
    (α : Cor.mk X ⟶ Cor.mk Y) (q : Y ⟶ V)
    (b : pullback (C := Scheme) X.hom V.hom)
    (hb : ((α ≫ (graphFunctor k).map q).val b) ≠ 0)
    (t : (integralComponentAt b).subscheme) :
    ∃ a : α.property.1.toFinset, ∃ d : (integralComponentAt a.val).subscheme,
      ((integralComponentAt a.val).subschemeι ≫ pullback.fst X.hom Y.hom) d =
        ((integralComponentAt b).subschemeι ≫ pullback.fst X.hom V.hom) t ∧
      q.left (((integralComponentAt a.val).subschemeι ≫ pullback.snd X.hom Y.hom) d) =
        ((integralComponentAt b).subschemeι ≫ pullback.snd X.hom V.hom) t := by
  obtain ⟨z, w, a, d, hs, hm, he⟩ :=
    exists_support_points_of_incidenceTorPairing_ne_zero X.hom Y.hom V.hom
      α ((graphFunctor k).map q) b hb t
  have hw : ((graphFunctor k).map q).val w.val ≠ 0 := by
    exact ((graphFunctor k).map q).property.1.mem_toFinset.mp w.property
  have hg := graphCorrespondenceOfComponents_projection_eq Y.hom V.hom q.left
    (MorphismProperty.Over.w q) (finite_genericPoints k (Cor.mk Y)) w.val hw d
  exact ⟨z, a, hs, (congrArg q.left hm).trans (hg.symm.trans he)⟩

end AlgebraicGeometry.Cor
