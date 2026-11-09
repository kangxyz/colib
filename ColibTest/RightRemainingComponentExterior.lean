/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingComponentExterior

/-! Literal endpoint consumers.  -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

example
    (t : correspondenceIncidence g h i w v) :
    (correspondenceRightRemainingSupportToImageExterior f g h i z w v t).ker =
      correspondenceRightRemainingImageComponent f g h i z w v t  := by
  exact correspondenceRightRemainingSupportToImageExterior_ker
    f g h i z w v t

example
    (t : correspondenceIncidence g h i w v) :
    IsPullback (correspondenceRightRemainingPairToImageIncidence f g h i z w v t)
      (correspondenceIncidenceToSupportProduct f g i z (correspondenceIncidenceMap g h i w v t))
      (correspondenceRightImageIncidenceInclusion f g h i z w v)
      (correspondenceRightRemainingSupportToImageExterior f g h i z w v t)  := by
  exact correspondenceRightRemainingPairToImageIncidence_isPullback
    f g h i z w v t

example
    (t : correspondenceIncidence g h i w v) :
    (correspondenceRightRemainingPairToImageIncidence f g h i z w v t).ker =
      (correspondenceRightRemainingImageComponent f g h i z w v t).comap
        (correspondenceRightImageIncidenceInclusion f g h i z w v)  := by
  exact correspondenceRightRemainingPairToImageIncidence_ker
    f g h i z w v t

end Stacks.Chow
