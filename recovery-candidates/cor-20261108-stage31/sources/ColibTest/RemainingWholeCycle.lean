/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingWholeCycle

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

example :
    letI := isFinite_correspondenceTripleToLeftImageIncidence f g h i z w v hz hw
    correspondenceLeftWeightedRemainingCycle f g h i z w v hw hv =
      finiteCyclePushforward (correspondenceTripleToLeftImageIncidence f g h i z w v)
        (correspondenceTripleIncidenceTorCycle K f g h i z w v hw hv) :=
  correspondenceLeftWeightedRemainingCycle_eq_tripleTorPushforward K f g h i z w v hz hw hv

example [IsSeparated i] :
    letI := isFinite_correspondenceTripleIncidenceMap f g h i z w v hz hw hv
    (incidenceTorPairing f h i
      (incidenceTorPairing f g h (singleFiniteCorrespondence f g z hz 1)
        (singleFiniteCorrespondence g h w hw 1))
      (singleFiniteCorrespondence h i v hv 1)).val =
        finiteCyclePushforward (correspondenceTripleIncidenceMap f g h i z w v)
          (correspondenceTripleIncidenceTorCycle K f g h i z w v hw hv) :=
  leftBracket_val_eq_finiteCyclePushforward_tripleTorCycle K f g h i z w v hz hw hv
