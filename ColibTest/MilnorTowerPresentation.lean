module

import Colib.RingTheory.KTheory.MilnorK.Norm.TowerPresentation

noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree

universe u

attribute [local instance] Ideal.Quotient.field
attribute [local instance] AdjoinRoot.instFactIrreduciblePolynomialPoly_colib

/-- The intermediate presentation preserves the given A-action on L and proves
composition for every native Milnor-ring element without a norm-law premise. -/
example
    {k A L : Type u} [Field k] [Field A] [Field L] [CharZero k]
    [Algebra k A] [Algebra A L] [Algebra k L] [IsScalarTower k A L]
    {d e : ℕ} (p : MonicIrreducibleOfDegree k d) (h : MonicIrreducibleOfDegree k e)
    (ε : A ≃ₐ[k] AdjoinRoot (poly p)) (η : L ≃ₐ[k] AdjoinRoot (poly h)) :
    ∃ (rDegree : ℕ) (r : MonicIrreducibleOfDegree A rDegree)
      (g : L ≃ₐ[A] AdjoinRoot (poly r)),
      ∀ x : MilnorKRing L,
        simpleMilnorNorm p
            (milnorKRingMap ε.toRingHom (simpleMilnorNorm r (milnorKRingMap g.toRingHom x))) =
          simpleMilnorNorm h (milnorKRingMap η.toRingHom x) :=
  exists_simpleMilnorNorm_tower_presentation p h ε η

end
