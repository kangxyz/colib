/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.CenterControl
public import Colib.AlgebraicGeometry.Correspondences.Graph.Functor

/-!
# All-point control under the actual graph functor

Every point of every surviving native graph component lies in the literal
closed graph. Combined with signed incidence provenance, this transports
specified centers through actual graph restriction. No flatness assumption
is needed for this point-control statement.

This is the native replacement for the graph point-control input in
`Motivic/Transfers/Sheaf/Germs/Pointed/Lifts/CorrespondenceAlgebra.lean`,
blob `d809712c6c984af6081bd2e5456c5d095f630c50`, at motivic revision
`a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow
open Function.locallyFinsuppWithin
open scoped BigOperators

universe u

namespace Stacks.Chow

/-- Every actual point of every native graph support component satisfies the
literal graph equation. The source may be disconnected or empty. -/
theorem graphCorrespondenceOfComponents_projection_eq
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) [IsSeparated g]
    (φ : X ⟶ Y) (hφ : φ ≫ g = f) (hX : (genericPoints X).Finite)
    (b : pullback (C := Scheme) f g)
    (hb : (graphCorrespondenceOfComponents f g φ hφ hX).val b ≠ 0)
    (t : (integralComponentAt b).subscheme) :
    ((integralComponentAt b).subschemeι ≫ pullback.snd f g) t =
      φ (((integralComponentAt b).subschemeι ≫ pullback.fst f g) t) := by
  classical
  let r := correspondenceGraphMap f g φ hφ
  let : IsClosedImmersion r := isClosedImmersion_correspondenceGraphMap f g φ hφ
  have hbR : b ∈ Set.range r := by
    by_contra hn
    apply hb
    change (∑ x ∈ hX.toFinset, single (r x) (1 : ℤ)) b = 0
    simp only [coe_sum, Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro x _
    have hx : b ≠ r x := fun he => hn ⟨x, he.symm⟩
    simp only [single_apply, hx, ite_false]
  have ht : (integralComponentAt b).subschemeι t ∈ closure ({b} : Set (pullback (C := Scheme) f g)) := by
    rw [← coe_support_integralComponentAt, ← (integralComponentAt b).range_subschemeι]
    exact Set.mem_range_self t
  have htR : (integralComponentAt b).subschemeι t ∈ Set.range r :=
    closure_minimal (Set.singleton_subset_iff.mpr hbR)
      r.isClosedEmbedding.isClosed_range ht
  obtain ⟨x, hx⟩ := htR
  change pullback.snd f g ((integralComponentAt b).subschemeι t) =
    φ (pullback.fst f g ((integralComponentAt b).subschemeι t))
  rw [← hx]
  have hfst : pullback.fst f g (r x) = x :=
    congrArg (fun a : X ⟶ X => a x) (correspondenceGraphMap_fst f g φ hφ)
  have hsnd : pullback.snd f g (r x) = φ x :=
    congrArg (fun a : X ⟶ Y => a x) (correspondenceGraphMap_snd f g φ hφ)
  rw [hfst, hsnd]

end Stacks.Chow

namespace AlgebraicGeometry.Cor

variable (k : Type u) [Field k]
  {U X Y : Scheme.SmoothSite (Spec (.of k))}

/-- Actual graph restriction preserves the designated target center of an
arbitrary signed correspondence at the specified source point. -/
theorem target_eq_of_graph_comp
    (α : Cor.mk X ⟶ Cor.mk Y) (q : U ⟶ X) (u : U.left) (y : Y.left)
    (hα : ∀ a : α.property.1.toFinset, ∀ t : (integralComponentAt a.val).subscheme,
      ((integralComponentAt a.val).subschemeι ≫ pullback.fst X.hom Y.hom) t = q.left u →
      ((integralComponentAt a.val).subschemeι ≫ pullback.snd X.hom Y.hom) t = y)
    (b : pullback (C := Scheme) U.hom Y.hom)
    (hb : (((graphFunctor k).map q ≫ α).val b) ≠ 0)
    (t : (integralComponentAt b).subscheme)
    (ht : ((integralComponentAt b).subschemeι ≫ pullback.fst U.hom Y.hom) t = u) :
    ((integralComponentAt b).subschemeι ≫ pullback.snd U.hom Y.hom) t = y := by
  obtain ⟨z, w, a, d, hs, hm, he⟩ :=
    exists_support_points_of_incidenceTorPairing_ne_zero U.hom X.hom Y.hom
      ((graphFunctor k).map q) α b hb t
  have hz : ((graphFunctor k).map q).val z.val ≠ 0 := by
    exact ((graphFunctor k).map q).property.1.mem_toFinset.mp z.property
  have hg := graphCorrespondenceOfComponents_projection_eq U.hom X.hom q.left
    (MorphismProperty.Over.w q) (finite_genericPoints k (Cor.mk U)) z.val hz a
  have hd : ((integralComponentAt w.val).subschemeι ≫ pullback.fst X.hom Y.hom) d =
      q.left u := hm.symm.trans (hg.trans (congrArg q.left (hs.trans ht)))
  exact he.symm.trans (hα w d hd)

end AlgebraicGeometry.Cor
