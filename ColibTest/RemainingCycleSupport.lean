/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingCycleSupport

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow

universe u

variable (K : Type u) [Field K] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
  (h : Z ⟶ Spec (.of K)) (i : W ⟶ Spec (.of K))
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  [Smooth f] [Smooth g] [Smooth h] [Smooth i] [IsSeparated g] [IsSeparated h]
  (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
  (hv : IsFiniteCorrespondencePoint h i v)

example (t : genericPoints (correspondenceIncidence f g h z w))
    (a : correspondenceIncidence f h i (correspondenceIncidenceMap f g h z w t.1) v)
    (ha : a ∈ genericPoints
      (correspondenceIncidence f h i (correspondenceIncidenceMap f g h z w t.1) v)) :
    correspondenceRemainingPairToImageIncidence f g h i z w v t.1 a ∈
      genericPoints (correspondenceLeftImageIncidence f g h i z w v) :=
  mem_genericPoints_correspondenceRemainingPairToImageIncidence f g h i z w v hz hw hv t a ha

example (x : correspondenceLeftImageIncidence f g h i z w v)
    (hx : x ∉ genericPoints (correspondenceLeftImageIncidence f g h i z w v)) :
    correspondenceLeftWeightedRemainingCycle f g h i z w v hw hv x = 0 :=
  correspondenceLeftWeightedRemainingCycle_eq_zero_of_not_generic f g h i z w v hz hw hv x hx
