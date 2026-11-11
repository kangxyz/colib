/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.TwoSourceBoundaryMatching

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Divisors
open AlgebraicGeometry.Scheme.RelativeCurvePencil

#check boundary_tensor_matching_two_sources
#check zeroScheme_boundary_after_sourceChange
#check zeroScheme_boundary_tensorSection_eq_top
