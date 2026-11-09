/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingWholeCycle

/-! Literal endpoint consumers.  -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingTheory.Sequence

universe u

namespace Stacks.Chow

variable (K : Type u) [Field K] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
  (h : Z ⟶ Spec (.of K)) (i : W ⟶ Spec (.of K))
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  [Smooth f] [Smooth g] [Smooth h] [Smooth i]
  [IsSeparated g] [IsSeparated h] [IsSeparated i]
  (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
  (hv : IsFiniteCorrespondencePoint h i v)

include hz

example :
    letI := isFinite_correspondenceTripleToRightImageIncidence f g h i z w v hw hv
    correspondenceRightWeightedRemainingCycle f g h i z w v hw hv =
      finiteCyclePushforward (correspondenceTripleToRightImageIncidence f g h i z w v)
        (correspondenceTripleIncidenceTorCycle K f g h i z w v hw hv)  := by
  exact correspondenceRightWeightedRemainingCycle_eq_tripleTorPushforward
    K f g h i z w v hz hw hv

example :
    letI := isFinite_correspondenceTripleIncidenceMap f g h i z w v hz hw hv
    (incidenceTorPairing f g i (singleFiniteCorrespondence f g z hz 1)
      (incidenceTorPairing g h i (singleFiniteCorrespondence g h w hw 1)
        (singleFiniteCorrespondence h i v hv 1))).val =
      finiteCyclePushforward (correspondenceTripleIncidenceMap f g h i z w v)
        (correspondenceTripleIncidenceTorCycle K f g h i z w v hw hv)  := by
  exact rightBracket_val_eq_finiteCyclePushforward_tripleTorCycle
    K f g h i z w v hz hw hv

end Stacks.Chow
