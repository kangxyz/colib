/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingExteriorMultiplicity

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
    [Flat (((integralComponentAt z).subschemeι ≫ pullback.snd f g) ≫ g)]
    (x : genericPoints (correspondenceRightIntermediateSupportProduct f g h i z w v)) :
    genericPoints (correspondenceIncidence g h i w v)  := by
  exact correspondenceRightExteriorGenericLabel
    f g h i z w v x

example
    [IsLocallyNoetherian (correspondenceRightIntermediateSupportProduct f g h i z w v)]
    (x : genericPoints (correspondenceRightIntermediateSupportProduct f g h i z w v)) :
    Module.length
      ((correspondenceRightIntermediateSupportProduct f g h i z w v).presheaf.stalk x.1)
      ((correspondenceRightIntermediateSupportProduct f g h i z w v).presheaf.stalk x.1 ⧸
        Ideal.map ((correspondenceRightExteriorProjection f g h i z w v).stalkMap x.1).hom
          (IsLocalRing.maximalIdeal ((correspondenceIncidence g h i w v).presheaf.stalk
            (correspondenceRightExteriorProjection f g h i z w v x.1)))) ≠ ⊤  := by
  exact length_correspondenceRightExteriorFiber_ne_top
    f g h i z w v x

end Stacks.Chow
