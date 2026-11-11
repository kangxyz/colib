/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.GeneratedWholeFieldPencil

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Ample Stacks.Divisors
open AlgebraicGeometry.Scheme.RelativeCurvePencil

#check WholeFieldSectionData.commonEnd_boundary_eq_start
#check WholeFieldSectionData.retainedFamily_finite_flat
#check WholeFieldSectionData.retainedPole_finite_relativeCartier
