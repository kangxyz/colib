/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightCommonImageSquare

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

example :
    IsPullback (correspondenceTripleToRightImageIncidence f g h i z w v)
      (correspondenceTripleIncidenceToRightSupportProduct f g h i z w v)
      (correspondenceRightImageIncidenceInclusion f g h i z w v)
      (correspondenceRightIntermediateImageMap f g h i z w v) := by
  exact correspondenceTripleToRightImageIncidence_isPullback
    f g h i z w v

end Stacks.Chow
