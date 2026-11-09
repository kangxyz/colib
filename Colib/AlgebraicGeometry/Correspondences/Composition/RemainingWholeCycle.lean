/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingCycleSupport
public import Colib.AlgebraicGeometry.Correspondences.Composition.TripleTorCycle
public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFiniteTripleCoefficient

/-!
# The whole actual weighted remaining cycle equals the pushed actual triple Tor cycle

Generic coefficients are the previously constructed full signed Tor comparison. The actual
source geometry proves both cycles vanish at every nongeneric point. Native cycle
extensionality therefore gives equality on the whole image incidence. The statement has no
chosen charts or lists, no coefficient or support hypothesis, and no additional finite-type
premise: local finite type is supplied by the original smooth factors and closed images.

Pushing through the literal final source-target map gives the actual left generator bracket's
native cycle. All original labels and residue degrees are retained. This is a full left-cycle
comparison; the right bracket, general bilinear associativity, and Cor category are not asserted.

References: Stacks 02R4 and 02R5 (actual finite pushforward and composition), 0AZT (Tor cycles),
and the local 0B1L statement used by the imported coefficient comparison. Independent source:
`kangxyz/motivic` at a6805c4a87cdfd7717dd7a94039246a167f15380,
Composition/Cycles/FirstStageWeightedRemainingCoefficient.lean, blob
3ae09238bac659f48c9e4beb21004af8f02ffd84, lines 205-245, and
Composition/Cycles/LeftComposition.lean, blob bb359ac96107367ce6acce86ebc152f78309ecb3,
lines 155-219. The native Mathlib cycle and actual stalk/Tor structures replace the old models.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable (K : Type u) [Field K] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
  (h : Z ⟶ Spec (.of K)) (i : W ⟶ Spec (.of K))
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  [Smooth f] [Smooth g] [Smooth h] [Smooth i] [IsSeparated g] [IsSeparated h]
  (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
  (hv : IsFiniteCorrespondencePoint h i v)

/-- The whole literal weighted remaining native cycle is the actual triple-Tor finite
pushforward, including the proven zero coefficients at all nongeneric whole-image points. -/
theorem correspondenceLeftWeightedRemainingCycle_eq_tripleTorPushforward :
    letI := isFinite_correspondenceTripleToLeftImageIncidence f g h i z w v hz hw
    correspondenceLeftWeightedRemainingCycle f g h i z w v hw hv =
      finiteCyclePushforward (correspondenceTripleToLeftImageIncidence f g h i z w v)
        (correspondenceTripleIncidenceTorCycle K f g h i z w v hw hv) := by
  let := isFinite_correspondenceTripleToLeftImageIncidence f g h i z w v hz hw
  let : LocallyOfFiniteType (correspondenceIntermediateImageTarget f g h z w ≫ h) := by
    dsimp only [correspondenceIntermediateImageTarget]
    infer_instance
  let : LocallyOfFiniteType
      (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h) := inferInstance
  apply Function.locallyFinsuppWithin.ext
  intro x
  by_cases hx : x ∈ genericPoints (correspondenceLeftImageIncidence f g h i z w v)
  · exact (correspondenceLeftWeightedRemainingCycle_eq_finsum_tripleTor
      K f g h i z w v hz hw hv ⟨x, hx⟩).trans
        (tripleTorPushforward_apply_generic K f g h i z w v hz hw hv ⟨x, hx⟩).symm
  · rw [correspondenceLeftWeightedRemainingCycle_eq_zero_of_not_generic
      f g h i z w v hz hw hv x hx,
      tripleTorPushforward_eq_zero_of_not_generic K f g h i z w v hz hw hv x hx]

/-- The actual nested left generator bracket has the literal final pushforward of the
full common triple-Tor cycle. This is not a right-bracket or associativity assertion. -/
theorem leftBracket_val_eq_finiteCyclePushforward_tripleTorCycle [IsSeparated i] :
    letI := isFinite_correspondenceTripleIncidenceMap f g h i z w v hz hw hv
    (incidenceTorPairing f h i
      (incidenceTorPairing f g h (singleFiniteCorrespondence f g z hz 1)
        (singleFiniteCorrespondence g h w hw 1))
      (singleFiniteCorrespondence h i v hv 1)).val =
        finiteCyclePushforward (correspondenceTripleIncidenceMap f g h i z w v)
          (correspondenceTripleIncidenceTorCycle K f g h i z w v hw hv) := by
  let := isFinite_correspondenceTripleIncidenceMap f g h i z w v hz hw hv
  let := isFinite_correspondenceTripleToLeftImageIncidence f g h i z w v hz hw
  let := isFinite_correspondenceLeftImageIncidenceMap f g h i z w v hz hw hv
  rw [← finiteCyclePushforward_weightedRemainingCycle_eq_leftBracket
    f g h i z w v hw hv hz,
    correspondenceLeftWeightedRemainingCycle_eq_tripleTorPushforward
      K f g h i z w v hz hw hv,
    finiteCyclePushforward_comp_apply]
  simp only [correspondenceTripleToLeftImageIncidence_map]

end Stacks.Chow
