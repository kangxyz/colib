/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingImageExteriorSquare

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

example :
    IsPullback (correspondenceRightExteriorProjection f g h i z w v)
      (correspondenceRightIntermediateImageMap f g h i z w v)
      (correspondenceIncidenceMap g h i w v).toImage
      (correspondenceRightImageExteriorProjection f g h i z w v)  := by
  exact correspondenceRightIntermediateImageMap_isPullback
    f g h i z w v

end Stacks.Chow
