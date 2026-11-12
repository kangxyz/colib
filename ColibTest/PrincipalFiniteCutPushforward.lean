/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Principal.FiniteCutPushforward

/-! # Finite principal cuts retain nilpotents, generic degrees and image collisions -/

open AlgebraicGeometry CategoryTheory TopologicalSpace Stacks.Chow

universe u

section

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  (g : X ⟶ Y) [IsFinite g] [IsDominant g]

/-- A squared equation uses the full quotient, not its radical. -/
example (s : Γ(Y, ⊤)) (hs : s ≠ 0) (y : Y) (hy : Order.coheight y = 1)
    (hfiber : ∀ x : X, g.base x = y → Order.coheight x = 1) :
    (∑ᶠ x ∈ g.base ⁻¹' {y},
      ((Module.length (X.presheaf.stalk x)
        (X.presheaf.stalk x ⧸ Ideal.span
          {X.presheaf.germ ⊤ x (by trivial) (g.appTop (s ^ 2))})).toNat : ℤ) *
            (g.residueDegree x : ℤ)) =
      (g.residueDegree (genericPoint X) : ℤ) *
        ((Module.length (Y.presheaf.stalk y)
          (Y.presheaf.stalk y ⧸ Ideal.span
            {Y.presheaf.germ ⊤ y (by trivial) (s ^ 2)})).toNat : ℤ) :=
  finsum_principalCutLength_mul_residueDegree g _ (pow_ne_zero 2 hs) y hy hfiber

/-- Any original signed coefficient and later image degree multiply the entire
finite fibre identity, retaining every colliding source point. -/
example (F : Y.functionField) (hF : F ≠ 0) (y : Y) (hy : Order.coheight y = 1)
    (hfiber : ∀ x : X, g.base x = y → Order.coheight x = 1)
    (weight : ℤ) (degree : ℕ) :
    weight * (∑ᶠ x ∈ g.base ⁻¹' {y},
      X.ord (dominantFunctionFieldMap g F) x * (g.residueDegree x : ℤ)) * degree =
      weight * ((g.residueDegree (genericPoint X) : ℤ) * Y.ord F y) * degree := by
  rw [finsum_ord_pullback_mul_residueDegree g F hF y hy hfiber]

end

#print axioms Stacks.Chow.finsum_ord_pullback_mul_residueDegree
#print axioms Stacks.Chow.dominantFunctionFieldMap_globalSection
#print axioms Stacks.Chow.ord_globalSection_eq_length
#print axioms Stacks.Chow.finsum_principalCutLength_mul_residueDegree
