/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.CommonBoundaryGeometry

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Divisors
open AlgebraicGeometry.Scheme.RelativeCurvePencil

#check commonToLambda_isPullback
#check commonToPsi_isPullback
#check commonBoundaryToLambda_inclusion
#check commonBoundaryToPsi_inclusion
