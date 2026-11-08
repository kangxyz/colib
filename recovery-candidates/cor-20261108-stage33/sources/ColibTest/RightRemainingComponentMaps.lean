/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingComponentMaps

/-! Literal endpoint consumers. Source-only; no compilation or kernel check performed. -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

example
    (t : correspondenceIncidence g h i w v) :
    correspondenceRightRemainingImagePointInclusion g h i w v t ≫
        (correspondenceIncidenceMap g h i w v).imageι =
      (integralComponentAt (correspondenceIncidenceMap g h i w v t)).subschemeι := by
  exact correspondenceRightRemainingImagePointInclusion_imageι
    g h i w v t

example
    (t : correspondenceIncidence g h i w v) :
    correspondenceRightRemainingPairToImageIncidence f g h i z w v t ≫
        correspondenceRightImageIncidenceMap f g h i z w v =
      correspondenceIncidenceMap f g i z (correspondenceIncidenceMap g h i w v t) := by
  exact correspondenceRightRemainingPairToImageIncidence_map
    f g h i z w v t

end Stacks.Chow
