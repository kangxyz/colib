/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingWeightedCycleEuler
public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingFiniteTripleEuler
public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingCycleSupport

/-!
# The whole actual right weighted remaining cycle equals the same actual triple Tor

The full actual Gamma-family Euler joins the literal right weighted coefficient
to the same existing sixfold triple Tor pushforward. Original smooth-diagonal
geometry supplies the Y list, and both actual cycles have already proved zero
coefficients at nongeneric points. Native cycle extensionality yields the whole
cycle equality without caller-supplied comparison, regular list or support input.
The literal final map then gives the original nested right generator bracket.

Mathematical references: Stacks 02RG, 02R4-02R5, 0AZT and local 0B1L.
Independent software source: kangxyz/motivic a6805c4a87cdfd7717dd7a94039246a167f15380,
Composition/Cycles/RightFirstStageWeightedRemainingCoefficient.lean,
blob 5771cc85d24a32f3610872f2a94d457154d1673b, and
Composition/Incidence/RightComposition.lean, blob 856b38b20a15444e6491366eb2406f21124bfdc5.
This is a right generator-cycle comparison; general signed associativity and
Cor category construction are separate consumers, not hypotheses here.
-/

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

/-- Each generic weighted right coefficient is the actual full triple-Tor pushforward. -/
theorem correspondenceRightWeightedRemainingCycle_apply_generic_eq_tripleTorPushforward
    (x : genericPoints (correspondenceRightImageIncidence f g h i z w v)) :
    letI := isFinite_correspondenceTripleToRightImageIncidence f g h i z w v hw hv
    correspondenceRightWeightedRemainingCycle f g h i z w v hw hv x.1 =
      finiteCyclePushforward (correspondenceTripleToRightImageIncidence f g h i z w v)
        (correspondenceTripleIncidenceTorCycle K f g h i z w v hw hv) x.1 := by
  let := isFinite_correspondenceTripleToRightImageIncidence f g h i z w v hw hv
  obtain ⟨r, s, hsr, hs⟩ :=
    exists_correspondenceRightRemainingOriginalMiddleList f g h i z w v x.1
  exact (finsum_signed_seqEuler_correspondenceRightRemainingFiniteTorModule_weightedCycle
    K f g h i z w v hz hw hv x s hsr hs).symm.trans
      (finsum_signed_correspondenceRightRemainingFiniteTorEuler_eq_tripleTorPushforward
        K f g h i z w v hz hw hv x s hsr hs)

/-- Full actual right cycle equality, including all proved nongeneric zero coefficients. -/
theorem correspondenceRightWeightedRemainingCycle_eq_tripleTorPushforward :
    letI := isFinite_correspondenceTripleToRightImageIncidence f g h i z w v hw hv
    correspondenceRightWeightedRemainingCycle f g h i z w v hw hv =
      finiteCyclePushforward (correspondenceTripleToRightImageIncidence f g h i z w v)
        (correspondenceTripleIncidenceTorCycle K f g h i z w v hw hv) := by
  let := isFinite_correspondenceTripleToRightImageIncidence f g h i z w v hw hv
  apply Function.locallyFinsuppWithin.ext
  intro x
  by_cases hx : x ∈ genericPoints (correspondenceRightImageIncidence f g h i z w v)
  · exact correspondenceRightWeightedRemainingCycle_apply_generic_eq_tripleTorPushforward
      K f g h i z w v hz hw hv ⟨x, hx⟩
  · rw [correspondenceRightWeightedRemainingCycle_eq_zero_of_not_generic
      f g h i z w v hz hw hv x hx,
      rightTripleTorPushforward_eq_zero_of_not_generic K f g h i z w v hz hw hv x hx]

/-- The literal nested right generator bracket has the same actual triple-Tor final pushforward. -/
theorem rightBracket_val_eq_finiteCyclePushforward_tripleTorCycle :
    letI := isFinite_correspondenceTripleIncidenceMap f g h i z w v hz hw hv
    (incidenceTorPairing f g i (singleFiniteCorrespondence f g z hz 1)
      (incidenceTorPairing g h i (singleFiniteCorrespondence g h w hw 1)
        (singleFiniteCorrespondence h i v hv 1))).val =
      finiteCyclePushforward (correspondenceTripleIncidenceMap f g h i z w v)
        (correspondenceTripleIncidenceTorCycle K f g h i z w v hw hv) := by
  let := isFinite_correspondenceTripleIncidenceMap f g h i z w v hz hw hv
  let := isFinite_correspondenceTripleToRightImageIncidence f g h i z w v hw hv
  let := isFinite_correspondenceRightImageIncidenceMap f g h i z w v hz hw hv
  rw [← finiteCyclePushforward_rightWeightedRemainingCycle_eq_rightBracket
    f g h i z w v hw hv hz,
    correspondenceRightWeightedRemainingCycle_eq_tripleTorPushforward K f g h i z w v hz hw hv,
    finiteCyclePushforward_comp_apply]
  simp only [correspondenceTripleToRightImageIncidence_map]

end Stacks.Chow
