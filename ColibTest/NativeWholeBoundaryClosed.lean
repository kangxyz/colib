/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.WholeBoundaryClosed

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Ample Stacks.Divisors
open AlgebraicGeometry.Scheme.RelativeCurvePencil

#check fullGraphBoundary_isClosedImmersion
#check fullGraphBoundary_isFinite
#check psiBoundary_closed
