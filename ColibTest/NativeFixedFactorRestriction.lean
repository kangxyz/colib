/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
import Colib.AlgebraicGeometry.RelativeCurve.Pencils.FixedFactorRestriction
open CategoryTheory AlgebraicGeometry Stacks.Ample
open AlgebraicGeometry.Scheme.RelativeCurvePencil
universe u
variable {X S Z : Scheme.{u}} (f : X ⟶ S)
  [IsAffine S] [IsLocallyNoetherian S] [IsProper f]
  (L : X.Modules) [IsInvertibleModule X L] (hL : IsAmple X L)
  (i : Z ⟶ X) [IsClosedImmersion i] (F : X.Modules) [IsInvertibleModule X F]
example : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Function.Surjective
    (pullbackGlobalSections i
      ((Stacks.AlgebraicGeometry.RelativeSerreVanishing.twistFunctor L (n : ℤ)).obj F)) :=
  exists_eventually_surjective_fixedFactor_boundary_restriction f L hL i F
#check fixedFactorTwistIso
#check exists_eventually_fixedFactor_boundary_pair
