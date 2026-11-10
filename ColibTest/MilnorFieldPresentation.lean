module

import Colib.RingTheory.KTheory.MilnorK.Norm.FieldPresentation

noncomputable section
open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree
universe u
attribute [local instance] Ideal.Quotient.field

/-- A finite separable extension has a presentation by the literal polynomial quotient. -/
example (k L : Type u) [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] [Algebra.IsSeparable k L] :
    ∃ (d : ℕ) (p : MonicIrreducibleOfDegree k d),
      Nonempty (L ≃ₐ[k] (k[X] ⧸ Ideal.span {poly p})) := by
  exact exists_monicIrreducible_presentation k L

end
