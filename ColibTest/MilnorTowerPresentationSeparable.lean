/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Norm.TowerPresentationSeparable

noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree

universe u

attribute [local instance] Ideal.Quotient.field
attribute [local instance] AdjoinRoot.instFactIrreduciblePolynomialPoly_colib

/-- The intermediate presentation preserves the given A-action on L and proves
composition for every native Milnor-ring element without a norm-law premise. -/
example
    {k A L : Type u} [Field k] [Field A] [Field L]
    [Algebra k A] [Algebra A L] [Algebra k L] [IsScalarTower k A L]
    [Algebra.IsSeparable k L]
    {d e : ℕ} (p : MonicIrreducibleOfDegree k d) (h : MonicIrreducibleOfDegree k e)
    (ε : A ≃ₐ[k] AdjoinRoot (poly p)) (η : L ≃ₐ[k] AdjoinRoot (poly h)) :
    ∃ (rDegree : ℕ) (r : MonicIrreducibleOfDegree A rDegree)
      (g : L ≃ₐ[A] AdjoinRoot (poly r)),
      ∀ x : MilnorKRing L,
        simpleMilnorNorm p
            (milnorKRingMap ε.toRingHom (simpleMilnorNorm r (milnorKRingMap g.toRingHom x))) =
          simpleMilnorNorm h (milnorKRingMap η.toRingHom x) :=
  exists_simpleMilnorNorm_tower_presentation_of_isSeparable p h ε η

end
