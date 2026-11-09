/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingFiniteTorModule

/-! Literal endpoint consumers.  -/

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

example [IsSeparated h] [IsSeparated i]
    [IsLocallyNoetherian (correspondenceIntersectionAmbient g h i)]
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v)
    (x : correspondenceRightImageIncidence f g h i z w v) (n : ℕ) :
    Module.Finite (correspondenceRightRemainingFiniteRing f g h i z w v x)
      (correspondenceRightRemainingFiniteTorModule f g h i z w v x n) := by
  exact moduleFinite_correspondenceRightRemainingFiniteTorModule
    f g h i z w v hw hv x n

end Stacks.Chow
