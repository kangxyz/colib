/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingImageComponentTor
public import Colib.AlgebraicGeometry.Correspondences.Composition.TorCycleImages
public import Colib.RingTheory.Koszul.EulerVanishing

/-!
# Full component quotient Euler is the actual remaining-cycle coefficient

At a generic point of the whole image incidence, the Euler of the full
image-component exterior quotient equals the coefficient of the actual
remaining pair Tor cycle pushed by its actual closed embedding. If the point
belongs to that closed image, its unique preimage is a genuine generic pair
label, and the proved ordered-list Tor comparison computes its coefficient.
If it does not belong, the actual component ideal stalk is the unit ideal,
so both the quotient Euler and the pushed coefficient vanish.

This attaches the actual remaining cycle to the quotient, including the empty
component fibre. No point preimage, genericity of an invented label, or Euler
comparison is supplied. Closed-immersion pushforward is the native finite
pushforward of Stacks 02R4; its residue degree is one for that geometric reason.
The full exterior quotient is not reduced.

Implementation target: motivic revision a6805c4a87cdfd7717dd7a94039246a167f15380,
Composition/Cycles/RightFirstStageWeightedRemainingCoefficient.lean, blob
5771cc85d24a32f3610872f2a94d457154d1673b, the component attachment used by
`rightImageIncidenceTorCycleCoefficient_eq_weightedRemainingIncidence` (lines 107-260).
The native `AlgebraicCycle` and categorical Tor replace the original separate
cycle and recursive Koszul models. This leaf does not assert the triple-side
coefficient equality or a completed associativity law.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency true

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingTheory.Sequence

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace Stacks.Chow

variable (K : Type u) [Field K] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
  (h : Z ⟶ Spec (.of K)) (i : W ⟶ Spec (.of K))
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  [Smooth f] [Smooth g] [Smooth h] [Smooth i]
  [IsSeparated g] [IsSeparated i]
  (hw : IsFiniteCorrespondencePoint g h w)
  (hv : IsFiniteCorrespondencePoint h i v)

include hw hv

/-- The full remaining component quotient computes the actual native closed-pushforward
Tor coefficient, including zero when the component has no point over the chosen generic label. -/
theorem seqEuler_correspondenceRightRemainingImageComponent_eq_pushforward_TorCycle
    (t : genericPoints (correspondenceIncidence g h i w v))
    (x : correspondenceRightImageIncidence f g h i z w v)
    (hx : x ∈ genericPoints (correspondenceRightImageIncidence f g h i z w v)) {r : ℕ}
    (s : Fin r → (pullback g g).presheaf.stalk
      (correspondenceRightImageMiddlePair f g h i z w v
        (correspondenceRightImageIncidenceInclusion f g h i z w v x)))
    (hsr : IsRegular ((pullback g g).presheaf.stalk
      (correspondenceRightImageMiddlePair f g h i z w v
        (correspondenceRightImageIncidenceInclusion f g h i z w v x))) (List.ofFn s))
    (hs : IdealSheafData.stalk (pullback.diagonal g).ker
      (correspondenceRightImageMiddlePair f g h i z w v
        (correspondenceRightImageIncidenceInclusion f g h i z w v x)) = Ideal.span (Set.range s)) :
    Koszul.seqEuler
        (fun a => correspondenceRightRemainingImageMiddleStalkMap f g h i z w v x (s a))
        (correspondenceRightRemainingImageComponentStalk f g h i z w v x t.1) =
      finiteCyclePushforward (correspondenceRightRemainingPairToImageIncidence f g h i z w v t.1)
        (incidenceTorCycle f g i z (correspondenceIncidenceMap g h i w v t.1)
          (isFiniteCorrespondencePoint_correspondenceIncidenceMap_generic
            g h i w v hw hv t)) x := by
  let q := correspondenceIncidenceMap g h i w v t.1
  let hq := isFiniteCorrespondencePoint_correspondenceIncidenceMap_generic g h i w v hw hv t
  let L := correspondenceRightImageIncidence f g h i z w v
  let T := correspondenceRightIntermediateImageProduct f g h i z w v
  let D := correspondenceRightRemainingImageComponent f g h i z w v t.1
  let j := correspondenceRightRemainingPairToImageIncidence f g h i z w v t.1
  let jL := correspondenceRightImageIncidenceInclusion f g h i z w v
  let R := correspondenceRightRemainingImageStalk f g h i z w v x
  let Q := correspondenceRightRemainingImageComponentStalk f g h i z w v x t.1
  let α := correspondenceRightRemainingImageMiddleStalkMap f g h i z w v x
  classical
  by_cases hmem : x ∈ Set.range j
  · obtain ⟨y, rfl⟩ := hmem
    have hy := mem_genericPoints_correspondenceRightRemainingPair_of_image f g h i z w v t.1 y hx
    rw [finiteCyclePushforward_apply_of_isClosedImmersion]
    rw [show incidenceTorCycle f g i z q hq y =
      correspondenceIncidenceTorCoefficient K f g i z q ⟨y, hy⟩ from
        incidenceTorCycle_apply_generic f g i z q hq ⟨y, hy⟩]
    simpa only [correspondenceIncidenceTorCoefficient, correspondenceIncidenceTorTerm] using
      seqEuler_correspondenceRightRemainingPairImage_eq_finsum_Tor f g h i z w v t.1 y s hsr hs
  · have hout : jL x ∉ ((D).support : Set T) := by
      intro hxD
      have hcomap : x ∈ (((D).comap jL).support : Set L) := by
        rw [Scheme.IdealSheafData.support_comap]
        exact hxD
      rw [← correspondenceRightRemainingPairToImageIncidence_ker f g h i z w v t.1,
        Scheme.Hom.support_ker] at hcomap
      change x ∈ closure (Set.range j) at hcomap
      rw [(j).isClosedEmbedding.isClosed_range.closure_eq] at hcomap
      exact hmem hcomap
    have htop : IdealSheafData.stalk D (jL x) = ⊤ :=
      (Stacks.Divisors.stalk_eq_top_iff_notMem_support D (jL x)).mpr hout
    have : Subsingleton Q := by
      change Subsingleton (R ⧸ IdealSheafData.stalk D (jL x))
      rw [htop]
      infer_instance
    have he := Koszul.seqEuler_eq_zero_of_subsingleton (fun a => α (s a)) Q
    have hc : finiteCyclePushforward j (incidenceTorCycle f g i z q hq) x = 0 := by
      by_contra hne
      obtain ⟨y, _, hy⟩ :=
        finiteCyclePushforward_support_subset j (incidenceTorCycle f g i z q hq) hne
      exact hmem ⟨y, hy⟩
    exact he.trans hc.symm

end Stacks.Chow
