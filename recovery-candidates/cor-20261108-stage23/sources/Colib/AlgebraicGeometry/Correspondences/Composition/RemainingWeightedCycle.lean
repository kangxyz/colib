/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFinalMap
public import Colib.AlgebraicGeometry.Correspondences.Composition.WeightedPairing

/-!
# Actual weighted remaining native cycle and its final pushforward

The original generic first-incidence labels index a finite sum of actual
remaining incidence Tor cycles, pushed into the whole image incidence. Each
summand retains the original signed Tor coefficient and original residue degree.
This is a native `AlgebraicCycle`, with no replacement cycle representation.

Functorial finite pushforward along the proved actual final map identifies this
cycle's final image with the existing left native Tor pairing, by its accepted
`WeightedPairing` expansion. This geometric assembly alone does not identify the
weighted cycle with the canonical common-triple Tor cycle.

Source target: motivic a6805c4a87cdfd7717dd7a94039246a167f15380,
Composition/Cycles/LeftComposition.lean, blob bb359ac96107367ce6acce86ebc152f78309ecb3,
lines 132-189. Only actual weighted-sum and final-map transport are implemented
here; the separate triple-to-weighted comparison is not assumed. Native finite
pushforward uses Stacks 02R4 and its composition law 02R5.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Function.locallyFinsuppWithin

universe u

namespace Stacks.Chow

variable {K : Type u} [Field K] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
  (h : Z ⟶ Spec (.of K)) (i : W ⟶ Spec (.of K))
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  [Smooth f] [Smooth g] [Smooth h] [Smooth i] [IsSeparated g] [IsSeparated h]
  (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v)

local notation3 (prettyPrint := false) "I" => correspondenceIncidence f g h z w
local notation3 (prettyPrint := false) "L" => correspondenceLeftImageIncidence f g h i z w v
local notation3 (prettyPrint := false) "r" => correspondenceIncidenceMap f g h z w

/-- The genuine labelled weighted remaining Tor cycle on the whole image incidence. -/
def correspondenceLeftWeightedRemainingCycle : AlgebraicCycle L ℤ :=
  letI := (finite_genericPoints_correspondenceIncidence_of_smooth f g h z w hw).fintype
  ∑ t : genericPoints I,
    (correspondenceIncidenceTorCoefficient K f g h z w t * ((r).residueDegree t.1 : ℤ)) •
      finiteCyclePushforward (correspondenceRemainingPairToImageIncidence f g h i z w v t.1)
        (incidenceTorCycle f h i (r t.1) v hv)

/-- Every original labelled component contributes its actual pushed coefficient. -/
theorem correspondenceLeftWeightedRemainingCycle_apply (x : L) :
    correspondenceLeftWeightedRemainingCycle f g h i z w v hw hv x =
      letI := (finite_genericPoints_correspondenceIncidence_of_smooth f g h z w hw).fintype
      ∑ t : genericPoints I,
        (correspondenceIncidenceTorCoefficient K f g h z w t * ((r).residueDegree t.1 : ℤ)) *
          finiteCyclePushforward (correspondenceRemainingPairToImageIncidence f g h i z w v t.1)
            (incidenceTorCycle f h i (r t.1) v hv) x := by
  classical
  let := (finite_genericPoints_correspondenceIncidence_of_smooth f g h z w hw).fintype
  simp only [correspondenceLeftWeightedRemainingCycle, coe_sum, Finset.sum_apply,
    coe_zsmul, Pi.smul_apply, zsmul_eq_mul]

/-- The final pushforward is the existing actual left native pairing, with all original
weights and labels. This does not assume or assert the canonical triple comparison. -/
theorem finiteCyclePushforward_weightedRemainingCycle_eq_leftPairing [IsSeparated i]
    (hz : IsFiniteCorrespondencePoint f g z) :
    letI := isFinite_correspondenceLeftImageIncidenceMap f g h i z w v hz hw hv
    finiteCyclePushforward (correspondenceLeftImageIncidenceMap f g h i z w v)
        (correspondenceLeftWeightedRemainingCycle f g h i z w v hw hv) =
      (incidenceTorPairing f h i (incidenceTorCorrespondence f g h z w hz hw)
        (singleFiniteCorrespondence h i v hv 1)).val := by
  classical
  let := isFinite_correspondenceLeftImageIncidenceMap f g h i z w v hz hw hv
  let := (finite_genericPoints_correspondenceIncidence_of_smooth f g h z w hw).fintype
  rw [incidenceTorPairing_left_eq_weightedRemaining]
  change finiteCyclePushforward (correspondenceLeftImageIncidenceMap f g h i z w v)
      (∑ t : genericPoints I,
        (correspondenceIncidenceTorCoefficient K f g h z w t * ((r).residueDegree t.1 : ℤ)) •
          finiteCyclePushforward (correspondenceRemainingPairToImageIncidence f g h i z w v t.1)
            (incidenceTorCycle f h i (r t.1) v hv)) =
    (finiteCorrespondences f i).subtype
      (∑ t : genericPoints I,
        (correspondenceIncidenceTorCoefficient K f g h z w t * ((r).residueDegree t.1 : ℤ)) •
          incidenceTorCorrespondence f h i (r t.1) v
            (isFiniteCorrespondencePoint_correspondenceIncidenceMap_generic f g h z w hz hw t) hv)
  simp only [map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro t _
  apply congrArg (fun a : AlgebraicCycle (pullback f i) ℤ =>
    (correspondenceIncidenceTorCoefficient K f g h z w t * ((r).residueDegree t.1 : ℤ)) • a)
  rw [finiteCyclePushforward_comp_apply, correspondenceRemainingPairToImageIncidence_map]
  exact (incidenceTorCorrespondence_val f h i (r t.1) v
    (isFiniteCorrespondencePoint_correspondenceIncidenceMap_generic f g h z w hz hw t) hv).symm

/-- The literal left bracketing on three generator cycles has the same actual final cycle. -/
theorem finiteCyclePushforward_weightedRemainingCycle_eq_leftBracket [IsSeparated i]
    (hz : IsFiniteCorrespondencePoint f g z) :
    letI := isFinite_correspondenceLeftImageIncidenceMap f g h i z w v hz hw hv
    finiteCyclePushforward (correspondenceLeftImageIncidenceMap f g h i z w v)
        (correspondenceLeftWeightedRemainingCycle f g h i z w v hw hv) =
      (incidenceTorPairing f h i
        (incidenceTorPairing f g h (singleFiniteCorrespondence f g z hz 1)
          (singleFiniteCorrespondence g h w hw 1))
        (singleFiniteCorrespondence h i v hv 1)).val := by
  rw [incidenceTorPairing_single_one]
  exact finiteCyclePushforward_weightedRemainingCycle_eq_leftPairing f g h i z w v hw hv hz

end Stacks.Chow
