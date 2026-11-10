/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Exterior.IncidenceProduct

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme Stacks.Chow

universe u
variable {S : Scheme.{u}} (X Y Z T : SmoothSite S)
  (z : pullback (C := Scheme) X.hom Y.hom)
  (w : pullback (C := Scheme) Y.hom Z.hom)

-- Arbitrary base, arbitrary support points, and no geometric-integrality assumption.
example : exteriorIncidenceProductFirst X Y Z T z w ≫
      exteriorIdentityTarget X Y T (integralComponentAt z) =
    exteriorIncidenceProductSecond X Y Z T z w ≫
      exteriorIdentitySource Y Z T (integralComponentAt w) :=
  exteriorIncidenceProduct_condition X Y Z T z w

example {W : Scheme.{u}} {f g : W ⟶
    pullback (correspondenceIncidenceLeft X.hom Y.hom Z.hom z w ≫ X.hom) T.hom}
    (h₁ : f ≫ exteriorIncidenceProductFirst X Y Z T z w =
      g ≫ exteriorIncidenceProductFirst X Y Z T z w)
    (h₂ : f ≫ exteriorIncidenceProductSecond X Y Z T z w =
      g ≫ exteriorIncidenceProductSecond X Y Z T z w) : f = g :=
  exteriorIncidenceProduct_hom_ext X Y Z T z w h₁ h₂
