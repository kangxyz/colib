/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingImageComponentCycle

/-! Literal endpoint consumers.  -/

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
  [IsSeparated g] [IsSeparated h] [IsSeparated i]
  (hw : IsFiniteCorrespondencePoint g h w)
  (hv : IsFiniteCorrespondencePoint h i v)

include hw hv

example
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
            g h i w v hw hv t)) x  := by
  exact seqEuler_correspondenceRightRemainingImageComponent_eq_pushforward_TorCycle
    K f g h i z w v hw hv t x hx s hsr hs

end Stacks.Chow
