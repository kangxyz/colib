/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph.RestrictionPoints
public import Colib.AlgebraicGeometry.Correspondences.Support.TargetControl

/-!
# Native all-point target sets under actual graph restriction

This is the graph-restriction control used in motivic
`Motivic/Transfers/Sheaf/Germs/FiniteRepresentatives/SourceIndependence.lean`,
blob `bdf18ee5fb7a759876f106f6effb9440755b24ec`, at
`a6805c4a87cdfd7717dd7a94039246a167f15380`. It is derived from genuine signed
incidence provenance, with no supplied support law and no flatness restriction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow
open Function.locallyFinsuppWithin

universe u

namespace AlgebraicGeometry.Cor

/-- Actual graph restriction preserves an arbitrary designated target set at
the displayed point over the original source point. -/
theorem targetsIn_graph_comp
    (k : Type u) [Field k] {U X Y : Scheme.SmoothSite (Spec (.of k))}
    (α : Cor.mk X ⟶ Cor.mk Y) (q : U ⟶ X) (x : X.left) (u : U.left)
    (hu : q.left u = x) (T : Set Y.left)
    (hα : finiteCorrespondences.TargetsIn α x T) :
    finiteCorrespondences.TargetsIn ((graphFunctor k).map q ≫ α) u T := by
  intro b hb t ht
  obtain ⟨a, d, hs, hd⟩ := exists_support_point_of_graph_comp_ne_zero k α q b hb t
  rw [← hd]
  apply hα a.val ?_ d (hs.trans ((congrArg q.left ht).trans hu))
  simpa only [Set.Finite.mem_toFinset, support, Function.mem_support] using a.property

end AlgebraicGeometry.Cor
