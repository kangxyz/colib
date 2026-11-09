module

import Colib.RingTheory.KTheory.MilnorK.Norm.NestedScalarBranch

noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree

universe u v

attribute [local instance] Ideal.Quotient.field
attribute [local instance] AdjoinRoot.instFactIrreduciblePolynomialPoly_colib

/-- The actual selected branch satisfies the whole-ring pointwise law. -/
example
    {k K : Type u} [Field k] [Field K] [CharZero K]
    (φ : k →+* K) {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (h : MonicIrreducibleOfDegree k e)
    (f : AdjoinRoot (poly p) →ₐ[k] AdjoinRoot (poly h))
    (s : {s : Σ a : ℕ, MonicIrreducibleOfDegree K a //
      poly s.2 ∣ (poly h).map φ})
    {Ω : Type v} [Field Ω] [Algebra K Ω] [FiniteDimensional K Ω] [IsGalois K Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] (hG : IsPGroup ℓ (Ω ≃ₐ[K] Ω))
    (j : AdjoinRoot (poly s.1.2) →ₐ[K] Ω)
    (y : MilnorKRing (AdjoinRoot (poly ((AdjoinRoot.nestedScalarFactorIndexEquiv φ (poly p) (poly h)
      f s).2).1.2))) :
    simpleMilnorNorm ((AdjoinRoot.nestedScalarFactorIndexEquiv φ (poly p) (poly h) f s).1).1.2
      (simpleMilnorNorm ((AdjoinRoot.nestedScalarFactorIndexEquiv φ (poly p) (poly h) f s).2).1.2 y)
      =
      simpleMilnorNorm s.1.2 (milnorKRingMap ((AdjoinRoot.nestedScalarFactorQuotientEquiv φ (poly p)
        (poly h) f s)).toRingHom y) := by
  exact simpleMilnorNorm_nestedScalarFactor_pGroup_tower φ p h f s ℓ hG j y


end
