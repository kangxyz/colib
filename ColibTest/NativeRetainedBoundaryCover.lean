/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RetainedBoundaryCover

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Ample Stacks.Divisors
open AlgebraicGeometry.Scheme.RelativeCurvePencil

#check retainedProductInclusion_isPullback
#check commonBoundary_retained_cover
#check lambdaBoundary_retained_cover
#check psiBoundary_retained_cover
