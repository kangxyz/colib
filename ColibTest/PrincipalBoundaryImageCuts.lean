/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Principal.BoundaryImageCuts

/-! # Actual integral image cuts without a fibre-coheight or flatness certificate -/

open AlgebraicGeometry CategoryTheory TopologicalSpace Stacks.Chow

universe u

/-- Quasi-finiteness suffices for codimension-one fibre points. -/
example {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (m : X ⟶ Y) [LocallyQuasiFinite m] [IsDominant m]
    (x : X) (hx : Order.coheight (m x) = 1) : Order.coheight x = 1 :=
  m.coheight_eq_one_of_locallyQuasiFinite x hx

/-- The ambient target need not be integral and the ambient map need not be dominant.
A squared equation retains the full nonreduced source and target cuts. -/
example {X Y : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (m : X ⟶ Y) [IsFinite m]
    (s : Γ((integralComponentAt (m (genericPoint X))).subscheme, ⊤)) (hs : s ≠ 0)
    (y : (integralComponentAt (m (genericPoint X))).subscheme)
    (hy : Order.coheight y = 1) :
    (∑ᶠ x ∈ (integralImageMap m).base ⁻¹' {y},
      ((Module.length (X.presheaf.stalk x)
        (X.presheaf.stalk x ⧸ Ideal.span
          {X.presheaf.germ ⊤ x (by trivial) ((integralImageMap m).appTop (s ^ 2))})).toNat : ℤ) *
            (m.residueDegree x : ℤ)) =
      (m.residueDegree (genericPoint X) : ℤ) *
        ((Module.length
          ((integralComponentAt (m (genericPoint X))).subscheme.presheaf.stalk y)
          ((integralComponentAt (m (genericPoint X))).subscheme.presheaf.stalk y ⧸ Ideal.span
            {(integralComponentAt (m (genericPoint X))).subscheme.presheaf.germ ⊤ y
              (by trivial) (s ^ 2)})).toNat : ℤ) := by
  let := isIntegral_integralComponentAt (m (genericPoint X))
  exact integralImageMap_principalCutLength m _ (pow_ne_zero 2 hs) y hy

#print axioms AlgebraicGeometry.Scheme.Hom.strictMono_of_locallyQuasiFinite
#print axioms AlgebraicGeometry.Scheme.Hom.coheight_eq_one_of_locallyQuasiFinite
#print axioms Stacks.Chow.integralComponentMap_principalCutLength
#print axioms Stacks.Chow.integralImageMap_inclusion
#print axioms Stacks.Chow.integralImageMap_isFinite
#print axioms Stacks.Chow.integralImageMap_isDominant
#print axioms Stacks.Chow.integralImageMap_residueDegree
#print axioms Stacks.Chow.integralImageMap_principalCutLength
#print axioms Stacks.Chow.PrincipalBoundary.componentCorrespondence_cutCoefficient
