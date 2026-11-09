/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightTripleTorPushforward

/-! Literal endpoint consumers.  -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace Stacks.Chow

variable (K : Type u) [Field K] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
  (h : Z ⟶ Spec (.of K)) (i : W ⟶ Spec (.of K))
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i) [Smooth g] [Smooth h] [IsSeparated i]

example
    [Smooth f] [LocallyOfFiniteType i]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (hv : IsFiniteCorrespondencePoint h i v)
    (x : correspondenceRightImageIncidence f g h i z w v)
    (hx : x ∉ genericPoints (correspondenceRightImageIncidence f g h i z w v)) :
    letI := isFinite_correspondenceTripleToRightImageIncidence f g h i z w v hw hv
    finiteCyclePushforward (correspondenceTripleToRightImageIncidence f g h i z w v)
      (correspondenceTripleIncidenceTorCycle K f g h i z w v hw hv) x = 0 := by
  exact rightTripleTorPushforward_eq_zero_of_not_generic
    K f g h i z w v hz hw hv x hx

example
    (hw : IsFiniteCorrespondencePoint g h w)
    (hv : IsFiniteCorrespondencePoint h i v)
    (x : genericPoints (correspondenceRightImageIncidence f g h i z w v)) :
    letI := isFinite_correspondenceTripleToRightImageIncidence f g h i z w v hw hv
    finiteCyclePushforward (correspondenceTripleToRightImageIncidence f g h i z w v)
        (correspondenceTripleIncidenceTorCycle K f g h i z w v hw hv) x.1 =
      ∑ᶠ t : {t : genericPoints (correspondenceTripleIncidence f g h i z w v) //
        correspondenceTripleToRightImageIncidence f g h i z w v t.1 = x.1},
        (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
          ((Module.length (correspondenceTripleIncidenceAmbientStalk f g h i z w v t.1.1)
            (correspondenceTripleIncidenceTor f g h i z w v t.1.1 n)).toNat : ℤ)) *
          ((correspondenceTripleToRightImageIncidence f g h i z w v).residueDegree t.1.1 : ℤ) := by
  exact rightTripleTorPushforward_apply_generic
    K f g h i z w v hw hv x

end Stacks.Chow
