/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingFiniteTorCoefficient

/-! Literal endpoint consumers.  -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace Stacks.Chow

section GeneralBase

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

example
    [IsSeparated h] [IsSeparated i]
    [IsLocallyNoetherian (correspondenceIntersectionAmbient g h i)]
    [Flat (((integralComponentAt z).subschemeι ≫ pullback.snd f g) ≫ g)]
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v)
    (x : correspondenceRightImageIncidence f g h i z w v)
    (q : genericPoints (correspondenceRightRemainingFiniteModel f g h i z w v x)) (n : ℕ) :
    let p := (correspondenceRightRemainingFiniteGenericEquivMinPrime
      f g h i z w v hw hv x q).1
    ((Module.length (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl
        (correspondenceRightRemainingFiniteTorModule f g h i z w v x n))).toNat : ℤ) =
      ((Module.length
        (correspondenceIncidenceAmbientStalk g h i w v
          (correspondenceRightExteriorProjection f g h i z w v
            (correspondenceRightRemainingFiniteModelProjection f g h i z w v x q.1)))
        (correspondenceIncidenceAmbientTor g h i w v
          (correspondenceRightExteriorProjection f g h i z w v
            (correspondenceRightRemainingFiniteModelProjection f g h i z w v x q.1)) n)).toNat :
              ℤ) *
          (correspondenceRightExteriorFiberLength f g h i z w v
            (correspondenceRightRemainingFiniteModelProjection f g h i z w v x q.1) : ℤ)  := by
  exact natCast_length_localized_correspondenceRightRemainingFiniteTorModule
    f g h i z w v hw hv x q n

end GeneralBase

end Stacks.Chow
