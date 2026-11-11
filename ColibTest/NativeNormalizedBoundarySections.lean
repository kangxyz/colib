/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
import Colib.AlgebraicGeometry.RelativeCurve.Pencils.NormalizedBoundarySections
open CategoryTheory AlgebraicGeometry Stacks.Divisors Stacks.Ample
open AlgebraicGeometry.Scheme.RelativeCurvePencil
universe u
example {Z : Scheme.{u}} (M : Z.Modules) [IsInvertibleModule Z M]
    (e : M ≅ SheafOfModules.unit Z.ringCatSheaf) :
    zeroScheme Z M (e.inv.app ⊤ 1) = ⊤ := zeroScheme_inverse_frame M e
#check fixedFactorBoundaryIso
#check exists_eventually_normalized_boundary_sections
#check exists_eventually_normalized_boundary_divisors
#check finite_relativeCartier_of_boundary_zero
