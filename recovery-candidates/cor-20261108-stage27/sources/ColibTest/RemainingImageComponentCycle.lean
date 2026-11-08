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

local notation3 (prettyPrint := false) "q" => correspondenceIncidenceMap f g h z w t
local notation3 (prettyPrint := false) "N" => correspondenceIncidence f h i q v
local notation3 (prettyPrint := false) "L" => correspondenceLeftImageIncidence f g h i z w v
local notation3 (prettyPrint := false) "T" =>
  correspondenceLeftIntermediateImageProduct f g h i z w v
local notation3 (prettyPrint := false) "D" => correspondenceRemainingImageComponent f g h i z w v t
local notation3 (prettyPrint := false) "j" =>
  correspondenceRemainingPairToImageIncidence f g h i z w v t
local notation3 (prettyPrint := false) "jL" =>
  correspondenceLeftImageIncidenceInclusion f g h i z w v

variable (x : L)

local notation3 (prettyPrint := false) "R" => correspondenceRemainingImageStalk f g h i z w v x
local notation3 (prettyPrint := false) "Q" =>
  correspondenceRemainingImageComponentStalk f g h i z w v x t
local notation3 (prettyPrint := false) "α" =>
  correspondenceRemainingImageMiddleStalkMap f g h i z w v x
local notation3 (prettyPrint := false) "A" => (pullback h h).presheaf.stalk
  (correspondenceLeftImageMiddlePair f g h i z w v (jL x))

include hv

example
    (hx : x ∈ genericPoints L) {r : ℕ} (s : Fin r → A)
    (hsr : IsRegular A (List.ofFn s))
    (hs : IdealSheafData.stalk (pullback.diagonal h).ker
      (correspondenceLeftImageMiddlePair f g h i z w v (jL x)) = Ideal.span (Set.range s)) :
    Koszul.seqEuler (fun a => α (s a)) Q =
      finiteCyclePushforward j (incidenceTorCycle f h i q v hv) x :=
  seqEuler_correspondenceRemainingImageComponent_eq_pushforward_TorCycle
    K f g h i z w v hv t x hx s hsr hs

#check seqEuler_correspondenceRemainingImageComponent_eq_pushforward_TorCycle
