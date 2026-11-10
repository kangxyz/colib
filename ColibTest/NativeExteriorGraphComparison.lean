/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Exterior.GraphComparison

/-!
# In-package checks for native exterior GraphComparison
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme Stacks.Chow
universe u
variable {S : Scheme.{u}} (X Y : SmoothSite S)

example (W V : (pullback X.hom Y.hom).IdealSheafData)
    (hWI : IsIntegral W.subscheme) (hVI : IsIntegral V.subscheme)
    (φ : X ⟶ Y)
    (hW : exteriorSupportSourceProjection X Y W ≫ φ.left =
      exteriorSupportTargetProjection X Y W)
    (hV : exteriorSupportSourceProjection X Y V ≫ φ.left =
      exteriorSupportTargetProjection X Y V)
    (h : Set.range (exteriorSupportSourceProjection X Y W) =
      Set.range (exteriorSupportSourceProjection X Y V)) : W = V :=
  nativeIntegralGraphSupport_eq_of_sourceRange_eq X Y W V hWI hVI φ hW hV h
