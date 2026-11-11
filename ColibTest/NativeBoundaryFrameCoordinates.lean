/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.BoundaryFrameCoordinates

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Divisors
open AlgebraicGeometry.Scheme.RelativeCurvePencil

#check restrictComparison_framePullback
#check boundaryCoprodFrame_inl_coordinate
#check boundaryCoprodFrame_inr_coordinate
#check unitAutomorphism_coordinate_of_restriction
