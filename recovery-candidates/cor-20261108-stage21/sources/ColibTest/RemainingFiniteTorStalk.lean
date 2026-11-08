/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFiniteTorStalk

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

attribute [local instance 100000] HasDerivedCategory.standard

section

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

-- Only localization preserves length here; no flatness of the finite-image map is asserted.
example (x : correspondenceLeftImageIncidence f g h i z w v)
    (q : correspondenceRemainingFiniteModel f g h i z w v x) (n : ℕ) :
    Module.length ((correspondenceRemainingFiniteModel f g h i z w v x).presheaf.stalk q)
        ((correspondenceRemainingFiniteTorSheaf f g h i z w v x n).presheaf.stalk q) =
      Module.length ((correspondenceLeftIntermediateSupportProduct f g h i z w v).presheaf.stalk
        (correspondenceRemainingFiniteModelProjection f g h i z w v x q))
        ((correspondenceLeftExteriorTorSheaf f g h i z w v n).presheaf.stalk
          (correspondenceRemainingFiniteModelProjection f g h i z w v x q)) :=
  length_correspondenceRemainingFiniteTorSheaf_stalk f g h i z w v x q n

end

#check Stacks.Chow.length_correspondenceRemainingFiniteTorSheaf_stalk

#check Stacks.Chow.length_correspondenceLeftExteriorTorSheaf_stalk

#check Stacks.Chow.length_localized_correspondenceRemainingFiniteTorModule
