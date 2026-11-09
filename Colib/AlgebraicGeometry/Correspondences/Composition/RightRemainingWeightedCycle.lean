/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingComponentMaps
public import Colib.AlgebraicGeometry.Correspondences.Composition.WeightedPairing

/-!
# The actual labelled right weighted remaining cycle

The original G,H incidence generic points index the finite sum. Each term keeps its
original signed Tor coefficient and residue degree and pushes the actual remaining
F,image(G,H) Tor cycle through the actual closed map. Repeated image supports retain
separate labels. Functorial finite pushforward identifies its final image with the
existing literal right bracket. This does not identify it with the triple-Tor cycle.

References: Stacks 02R4-02R5 and independent motivic
 a6805c4a87cdfd7717dd7a94039246a167f15380, Composition/Incidence/RightComposition.lean.
-/

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
  [Smooth g] [Smooth h] [Smooth i] [IsSeparated i]
  (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v)

/-- The actual right weighted remaining cycle, before its final source-target pushforward. -/
def correspondenceRightWeightedRemainingCycle :
    AlgebraicCycle (correspondenceRightImageIncidence f g h i z w v) ℤ :=
  letI := (finite_genericPoints_correspondenceIncidence_of_smooth g h i w v hv).fintype
  ∑ t : genericPoints (correspondenceIncidence g h i w v),
    (correspondenceIncidenceTorCoefficient K g h i w v t *
      ((correspondenceIncidenceMap g h i w v).residueDegree t.1 : ℤ)) •
        finiteCyclePushforward (correspondenceRightRemainingPairToImageIncidence f g h i z w v t.1)
          (incidenceTorCycle f g i z (correspondenceIncidenceMap g h i w v t.1)
            (isFiniteCorrespondencePoint_correspondenceIncidenceMap_generic g h i w v hw hv t))

/-- The coefficient formula retains every original label, including image collisions. -/
theorem correspondenceRightWeightedRemainingCycle_apply
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
  classical
  let := (finite_genericPoints_correspondenceIncidence_of_smooth g h i w v hv).fintype
  simp only [correspondenceRightWeightedRemainingCycle, coe_sum, Finset.sum_apply,
    coe_zsmul, zsmul_eq_mul, Pi.mul_apply, Pi.intCast_apply, Int.cast_id]

/-- Pushing the actual right weighted cycle gives the original native right pairing. -/
theorem finiteCyclePushforward_rightWeightedRemainingCycle_eq_rightPairing
    (hz : IsFiniteCorrespondencePoint f g z) :
    letI := isFinite_correspondenceRightImageIncidenceMap f g h i z w v hz hw hv
    finiteCyclePushforward (correspondenceRightImageIncidenceMap f g h i z w v)
        (correspondenceRightWeightedRemainingCycle f g h i z w v hw hv) =
      (incidenceTorPairing f g i (singleFiniteCorrespondence f g z hz 1)
        (incidenceTorCorrespondence g h i w v hw hv)).val := by
  classical
  let := isFinite_correspondenceRightImageIncidenceMap f g h i z w v hz hw hv
  let := (finite_genericPoints_correspondenceIncidence_of_smooth g h i w v hv).fintype
  rw [incidenceTorPairing_right_eq_weightedRemaining]
  change finiteCyclePushforward (correspondenceRightImageIncidenceMap f g h i z w v)
      (∑ t : genericPoints (correspondenceIncidence g h i w v),
        (correspondenceIncidenceTorCoefficient K g h i w v t *
          ((correspondenceIncidenceMap g h i w v).residueDegree t.1 : ℤ)) •
            finiteCyclePushforward
              (correspondenceRightRemainingPairToImageIncidence f g h i z w v t.1)
              (incidenceTorCycle f g i z (correspondenceIncidenceMap g h i w v t.1)
                (isFiniteCorrespondencePoint_correspondenceIncidenceMap_generic
                  g h i w v hw hv t))) =
    (finiteCorrespondences f i).subtype
      (∑ t : genericPoints (correspondenceIncidence g h i w v),
        (correspondenceIncidenceTorCoefficient K g h i w v t *
          ((correspondenceIncidenceMap g h i w v).residueDegree t.1 : ℤ)) •
            incidenceTorCorrespondence f g i z (correspondenceIncidenceMap g h i w v t.1) hz
              (isFiniteCorrespondencePoint_correspondenceIncidenceMap_generic g h i w v hw hv t))
  simp only [map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro t _
  apply congrArg (fun a : AlgebraicCycle (pullback f i) ℤ =>
    (correspondenceIncidenceTorCoefficient K g h i w v t *
      ((correspondenceIncidenceMap g h i w v).residueDegree t.1 : ℤ)) • a)
  simpa only [finiteCyclePushforward_comp_apply,
    correspondenceRightRemainingPairToImageIncidence_map, AddSubgroup.subtype_apply] using
    (incidenceTorCorrespondence_val f g i z (correspondenceIncidenceMap g h i w v t.1) hz
      (isFiniteCorrespondencePoint_correspondenceIncidenceMap_generic g h i w v hw hv t)).symm

/-- The literal nested right bracket is the final image of the same actual weighted cycle. -/
theorem finiteCyclePushforward_rightWeightedRemainingCycle_eq_rightBracket
    (hz : IsFiniteCorrespondencePoint f g z) :
    letI := isFinite_correspondenceRightImageIncidenceMap f g h i z w v hz hw hv
    finiteCyclePushforward (correspondenceRightImageIncidenceMap f g h i z w v)
        (correspondenceRightWeightedRemainingCycle f g h i z w v hw hv) =
      (incidenceTorPairing f g i (singleFiniteCorrespondence f g z hz 1)
        (incidenceTorPairing g h i (singleFiniteCorrespondence g h w hw 1)
          (singleFiniteCorrespondence h i v hv 1))).val := by
  rw [incidenceTorPairing_single_one]
  exact finiteCyclePushforward_rightWeightedRemainingCycle_eq_rightPairing
    f g h i z w v hw hv hz

end Stacks.Chow
