/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingWeightedCycle

/-! Literal endpoint consumers. Source-only; no compilation or kernel check performed. -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Function.locallyFinsuppWithin

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace Stacks.Chow

variable {K : Type u} [Field K] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
  (h : Z ⟶ Spec (.of K)) (i : W ⟶ Spec (.of K))
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  [Smooth f] [Smooth g] [Smooth h] [Smooth i] [IsSeparated g] [IsSeparated h] [IsSeparated i]
  (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v)

example
    (x : correspondenceRightImageIncidence f g h i z w v) :
    correspondenceRightWeightedRemainingCycle f g h i z w v hw hv x =
      letI := (finite_genericPoints_correspondenceIncidence_of_smooth g h i w v hv).fintype
      ∑ t : genericPoints (correspondenceIncidence g h i w v),
        (correspondenceIncidenceTorCoefficient K g h i w v t *
          ((correspondenceIncidenceMap g h i w v).residueDegree t.1 : ℤ)) *
            finiteCyclePushforward
              (correspondenceRightRemainingPairToImageIncidence f g h i z w v t.1)
              (incidenceTorCycle f g i z (correspondenceIncidenceMap g h i w v t.1)
                (isFiniteCorrespondencePoint_correspondenceIncidenceMap_generic
                  g h i w v hw hv t)) x := by
  exact correspondenceRightWeightedRemainingCycle_apply
    f g h i z w v hw hv x

example
    (hz : IsFiniteCorrespondencePoint f g z) :
    letI := isFinite_correspondenceRightImageIncidenceMap f g h i z w v hz hw hv
    finiteCyclePushforward (correspondenceRightImageIncidenceMap f g h i z w v)
        (correspondenceRightWeightedRemainingCycle f g h i z w v hw hv) =
      (incidenceTorPairing f g i (singleFiniteCorrespondence f g z hz 1)
        (incidenceTorPairing g h i (singleFiniteCorrespondence g h w hw 1)
          (singleFiniteCorrespondence h i v hv 1))).val := by
  exact finiteCyclePushforward_rightWeightedRemainingCycle_eq_rightBracket
    f g h i z w v hw hv hz

end Stacks.Chow
