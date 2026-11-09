/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingFiniteGenericLabels

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
    (x : correspondenceRightImageIncidence f g h i z w v) :
    genericPoints (correspondenceRightRemainingFiniteModel f g h i z w v x) ≃
      correspondenceRightRemainingOriginalGenericLabels f g h i z w v x  := by
  exact correspondenceRightRemainingFiniteGenericEquivOriginal
    f g h i z w v x

example [IsSeparated i]
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v)
    (x : correspondenceRightImageIncidence f g h i z w v) :
    {q : PrimeSpectrum (correspondenceRightRemainingFiniteRing f g h i z w v x) // IsMin q} ≃
      correspondenceRightRemainingOriginalGenericLabels f g h i z w v x  := by
  exact correspondenceRightRemainingFiniteMinPrimeEquivOriginal
    f g h i z w v hw hv x

end Stacks.Chow
