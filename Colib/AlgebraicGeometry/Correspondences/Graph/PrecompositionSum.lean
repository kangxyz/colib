/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph.Functor

/-!
# The finite incidence presentation of graph precomposition

Expand only the native graph and the native signed finite support. The resulting
finite family consists of the original incidence Tor correspondences, with exactly
the original integer coefficients. The graph source may be empty or disconnected.
This presentation is used by the local Čech contraction; it introduces no new cycle.
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.Chow TopologicalSpace
open Function.locallyFinsuppWithin
open scoped BigOperators

universe u

namespace AlgebraicGeometry.Cor

variable (k : Type u) [Field k]
  {U X V : Scheme.SmoothSite (Spec (.of k))}

/-- The actual graph composed with one signed prime is its finite incidence sum. -/
theorem graph_comp_single_eq_sum_incidence (g : U ⟶ X)
    (z : CategoryTheory.Limits.pullback (C := Scheme) X.hom V.hom)
    (hz : IsFiniteCorrespondencePoint X.hom V.hom z) (n : ℤ) :
    let := (finite_genericPoints k (Cor.mk U)).fintype
    (graphFunctor k).map g ≫ singleFiniteCorrespondence X.hom V.hom z hz n =
      ∑ t : genericPoints U.left, n • incidenceTorCorrespondence U.hom X.hom V.hom
        (correspondenceGraphMap U.hom X.hom g.left (MorphismProperty.Over.w g) t.val) z
        (isFiniteCorrespondencePoint_graphMap U.hom X.hom g.left
          (MorphismProperty.Over.w g) t) hz := by
  classical
  let := (finite_genericPoints k (Cor.mk U)).fintype
  change (incidenceTorPairing U.hom X.hom V.hom).flip
    (singleFiniteCorrespondence X.hom V.hom z hz n)
    (graphCorrespondenceOfComponents U.hom X.hom g.left (MorphismProperty.Over.w g)
      (finite_genericPoints k (Cor.mk U))) = _
  rw [graphCorrespondenceOfComponents_eq_sum_singleFiniteCorrespondence, map_sum]
  apply Finset.sum_congr rfl
  intro t _
  exact (incidenceTorPairing_single U.hom X.hom V.hom _ z _ hz 1 n).trans
    (by rw [one_mul])

/-- Graph restriction of an arbitrary signed cycle has a finite presentation by its
actual incidence schemes, indexed by the original support and source components. -/
theorem graph_comp_eq_sum_incidence (α : Cor.mk X ⟶ Cor.mk V) (g : U ⟶ X) :
    let := (finite_genericPoints k (Cor.mk U)).fintype
    (graphFunctor k).map g ≫ α =
      ∑ i : ↥α.property.1.toFinset × genericPoints U.left,
        α.val i.1.val • incidenceTorCorrespondence U.hom X.hom V.hom
          (correspondenceGraphMap U.hom X.hom g.left
            (MorphismProperty.Over.w g) i.2.val) i.1.val
          (isFiniteCorrespondencePoint_graphMap U.hom X.hom g.left
            (MorphismProperty.Over.w g) i.2)
          (α.property.2 i.1.val (by
            simpa only [Set.Finite.mem_toFinset, support, Function.mem_support]
              using i.1.property)) := by
  classical
  let := (finite_genericPoints k (Cor.mk U)).fintype
  let I := ↥α.property.1.toFinset
  have hadm (z : I) : IsFiniteCorrespondencePoint X.hom V.hom z.val :=
    α.property.2 z.val (by
      simpa only [Set.Finite.mem_toFinset, support, Function.mem_support] using z.property)
  let c (z : I) (t : genericPoints U.left) : Cor.mk U ⟶ Cor.mk V :=
    α.val z.val • incidenceTorCorrespondence U.hom X.hom V.hom
      (correspondenceGraphMap U.hom X.hom g.left (MorphismProperty.Over.w g) t.val)
      z.val (isFiniteCorrespondencePoint_graphMap U.hom X.hom g.left
        (MorphismProperty.Over.w g) t) (hadm z)
  let F : finiteCorrespondences X.hom V.hom →+ finiteCorrespondences U.hom V.hom :=
    incidenceTorPairing U.hom X.hom V.hom ((graphFunctor k).map g)
  let d (z : I) : finiteCorrespondences X.hom V.hom :=
    singleFiniteCorrespondence X.hom V.hom z.val (hadm z) (α.val z.val)
  have hα : α = ∑ z : I, d z := finiteCorrespondence_eq_sum_signedSingles X.hom V.hom α
  have hsingle (z : I) : F (d z) = ∑ t : genericPoints U.left, c z t :=
    graph_comp_single_eq_sum_incidence k g z.val (hadm z) (α.val z.val)
  change F α = ∑ i : I × genericPoints U.left, c i.1 i.2
  refine (congrArg F hα).trans ((map_sum F d Finset.univ).trans ?_)
  exact (Finset.sum_congr rfl (fun z _ => hsingle z)).trans
    (Fintype.sum_prod_type (fun i : I × genericPoints U.left => c i.1 i.2)).symm

end AlgebraicGeometry.Cor
