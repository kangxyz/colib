/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Graph.PrecompositionSum

noncomputable section

open AlgebraicGeometry CategoryTheory Stacks.Chow TopologicalSpace
open Function.locallyFinsuppWithin
open scoped BigOperators

universe u

namespace AlgebraicGeometry.Cor

variable (k : Type u) [Field k]
  {U X V : Scheme.SmoothSite (Spec (.of k))}

example (α : Cor.mk X ⟶ Cor.mk V) (g : U ⟶ X) :
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
              using i.1.property)) :=
  graph_comp_eq_sum_incidence k α g

example (g : U ⟶ X) (α : Cor.mk X ⟶ Cor.mk V) :
    (graphFunctor k).map g ≫ (α - α) = 0 := by
  rw [sub_self]
  exact incidenceTorPairing_zero_right U.hom X.hom V.hom ((graphFunctor k).map g)

example (g : U ⟶ X) :
    (graphFunctor k).map g ≫ (0 : Cor.mk X ⟶ Cor.mk V) = 0 :=
  incidenceTorPairing_zero_right U.hom X.hom V.hom ((graphFunctor k).map g)

end AlgebraicGeometry.Cor
