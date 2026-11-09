/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingExteriorWeight

/-! Literal endpoint consumers.  -/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

example
    (C : ChowSituation.{u}) (sE : (correspondenceRightIntermediateSupportProduct f g h i z w v) ⟶
      C.S) [LocallyOfFiniteType sE]
    (η : genericPoints (correspondenceRightIntermediateSupportProduct f g h i z w v)) (j : ℤ) :
    let π := correspondenceRightExteriorProjection f g h i z w v
    flatPullbackWeight C sE π j η.1 =
      if relativeDimension C.dimensionFunction sE η.1 = j then
        (correspondenceRightExteriorFiberLength f g h i z w v η.1 : ℤ) else 0  := by
  exact flatPullbackWeight_correspondenceRightExterior_generic_grade
    f g h i z w v C sE η j

end Stacks.Chow
