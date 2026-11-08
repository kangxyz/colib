module

import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingImageComponentCycle

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow
open RingTheory.Sequence

universe u

attribute [local instance 100000] HasDerivedCategory.standard


variable (K : Type u) [Field K] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
  (h : Z ⟶ Spec (.of K)) (i : W ⟶ Spec (.of K))
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  [Smooth f] [Smooth h] [Smooth i] [IsSeparated h]
  (hv : IsFiniteCorrespondencePoint h i v)
  (t : correspondenceIncidence f g h z w)

include hv

example
    (x : correspondenceLeftImageIncidence f g h i z w v)
    (hx : x ∈ genericPoints (correspondenceLeftImageIncidence f g h i z w v)) {r : ℕ}
    (s : Fin r → (pullback h h).presheaf.stalk
      (correspondenceLeftImageMiddlePair f g h i z w v
        (correspondenceLeftImageIncidenceInclusion f g h i z w v x)))
    (hsr : IsRegular ((pullback h h).presheaf.stalk
      (correspondenceLeftImageMiddlePair f g h i z w v
        (correspondenceLeftImageIncidenceInclusion f g h i z w v x))) (List.ofFn s))
    (hs : IdealSheafData.stalk (pullback.diagonal h).ker
      (correspondenceLeftImageMiddlePair f g h i z w v
        (correspondenceLeftImageIncidenceInclusion f g h i z w v x)) = Ideal.span (Set.range s)) :
    Koszul.seqEuler
        (fun a => correspondenceRemainingImageMiddleStalkMap f g h i z w v x (s a))
        (correspondenceRemainingImageComponentStalk f g h i z w v x t) =
      finiteCyclePushforward (correspondenceRemainingPairToImageIncidence f g h i z w v t)
        (incidenceTorCycle f h i (correspondenceIncidenceMap f g h z w t) v hv) x :=
  seqEuler_correspondenceRemainingImageComponent_eq_pushforward_TorCycle
    K f g h i z w v hv t x hx s hsr hs

#check seqEuler_correspondenceRemainingImageComponent_eq_pushforward_TorCycle
