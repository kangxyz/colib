/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.RelativeCurve.Pencils.BoundaryRestriction

/-! Actual whole-boundary restriction scope checks. UNCOMPILED. -/

open CategoryTheory AlgebraicGeometry Stacks.Ample
open AlgebraicGeometry.Scheme.RelativeCurvePencil

universe u

example {X S Z : Scheme.{u}} (f : X ⟶ S)
    [IsAffine S] [IsLocallyNoetherian S] [IsProper f]
    (L : X.Modules) [IsInvertibleModule X L] (hL : IsAmple X L)
    (i : Z ⟶ X) [IsClosedImmersion i] :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Function.Surjective
      (pullbackGlobalSections i (tensorPowModule X L (n : ℤ))) :=
  exists_eventually_surjective_boundary_restriction f L hL i

#check exists_eventually_prescribed_boundary_section
#check exists_eventually_boundary_frame_section
