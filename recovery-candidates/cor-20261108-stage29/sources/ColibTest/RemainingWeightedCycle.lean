module

import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingWeightedCycle

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow TopologicalSpace
open Function.locallyFinsuppWithin

universe u


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

example (x : L) :
    correspondenceLeftWeightedRemainingCycle f g h i z w v hw hv x =
      letI := (finite_genericPoints_correspondenceIncidence_of_smooth f g h z w hw).fintype
      ∑ t : genericPoints I,
        (correspondenceIncidenceTorCoefficient K f g h z w t * ((r).residueDegree t.1 : ℤ)) *
          finiteCyclePushforward (correspondenceRemainingPairToImageIncidence f g h i z w v t.1)
            (incidenceTorCycle f h i (r t.1) v hv) x :=
  correspondenceLeftWeightedRemainingCycle_apply
    f g h i z w v hw hv x

example [IsSeparated i]
    (hz : IsFiniteCorrespondencePoint f g z) :
    letI := isFinite_correspondenceLeftImageIncidenceMap f g h i z w v hz hw hv
    finiteCyclePushforward (correspondenceLeftImageIncidenceMap f g h i z w v)
        (correspondenceLeftWeightedRemainingCycle f g h i z w v hw hv) =
      (incidenceTorPairing f h i (incidenceTorCorrespondence f g h z w hz hw)
        (singleFiniteCorrespondence h i v hv 1)).val :=
  finiteCyclePushforward_weightedRemainingCycle_eq_leftPairing
    f g h i z w v hw hv hz

example [IsSeparated i]
    (hz : IsFiniteCorrespondencePoint f g z) :
    letI := isFinite_correspondenceLeftImageIncidenceMap f g h i z w v hz hw hv
    finiteCyclePushforward (correspondenceLeftImageIncidenceMap f g h i z w v)
        (correspondenceLeftWeightedRemainingCycle f g h i z w v hw hv) =
      (incidenceTorPairing f h i
        (incidenceTorPairing f g h (singleFiniteCorrespondence f g z hz 1)
          (singleFiniteCorrespondence g h w hw 1))
        (singleFiniteCorrespondence h i v hv 1)).val :=
  finiteCyclePushforward_weightedRemainingCycle_eq_leftBracket
    f g h i z w v hw hv hz

#check correspondenceLeftWeightedRemainingCycle
#check correspondenceLeftWeightedRemainingCycle_apply
#check finiteCyclePushforward_weightedRemainingCycle_eq_leftPairing
#check finiteCyclePushforward_weightedRemainingCycle_eq_leftBracket
