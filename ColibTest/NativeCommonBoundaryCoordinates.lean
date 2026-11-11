/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.CommonBoundaryCoordinates

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Divisors
open AlgebraicGeometry.Scheme.RelativeCurvePencil

#check commonZero_polynomialMap_eq
#check commonZero_coordinate_eq
#check commonBoundary_coordinate_eq

example {X Y : Scheme} {r s : Γ(X ⨿ Y, ⊤)}
    (hl : (coprod.inl : X ⟶ X ⨿ Y).appTop r = (coprod.inl : X ⟶ X ⨿ Y).appTop s)
    (hr : (coprod.inr : Y ⟶ X ⨿ Y).appTop r = (coprod.inr : Y ⟶ X ⨿ Y).appTop s) : r = s :=
  globalSections_coprod_ext hl hr
