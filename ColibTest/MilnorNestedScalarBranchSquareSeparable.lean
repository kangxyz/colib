/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Norm.NestedScalarBranchSquareSeparable

noncomputable section
open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree
universe u v
attribute [local instance] Ideal.Quotient.field
attribute [local instance] AdjoinRoot.instFactIrreduciblePolynomialPoly_colib

/-- The actual coefficient-factor square gives the pointwise branch norm identity. -/
example
    {k K : Type u} [Field k] [Field K]
    (φ : k →+* K) {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (h : MonicIrreducibleOfDegree k e)
    (f : AdjoinRoot (poly p) →ₐ[k] AdjoinRoot (poly h))
    (s : {s : Σ a : ℕ, MonicIrreducibleOfDegree K a //
      poly s.2 ∣ (poly h).map φ})
    {Ω : Type v} [Field Ω] [Algebra K Ω] [FiniteDimensional K Ω] [IsGalois K Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] (hG : IsPGroup ℓ (Ω ≃ₐ[K] Ω))
    (j : AdjoinRoot (poly s.1.2) →ₐ[K] Ω)
    (x : MilnorKRing (AdjoinRoot (poly (AdjoinRoot.towerFactor (poly p) (poly h) f).1.2))) :
    let q := AdjoinRoot.towerFactor (poly p) (poly h) f
    let z := AdjoinRoot.nestedScalarFactorIndexEquiv φ (poly p) (poly h) f s
    let r : MonicIrreducibleOfDegree K z.1.1.1 := z.1.1.2
    let t : MonicIrreducibleOfDegree (AdjoinRoot (poly r)) z.2.1.1 := z.2.1.2
    let ι : AdjoinRoot (poly p) →+* AdjoinRoot (poly r) :=
      AdjoinRoot.map φ (poly p) (poly r) z.1.2
    let ρ : ((AdjoinRoot (poly p))[X] ⧸ Ideal.span {poly q.1.2}) →+*
        ((AdjoinRoot (poly r))[X] ⧸ Ideal.span {poly t}) :=
      AdjoinRoot.map ι (poly q.1.2) (poly t) z.2.2
    let θ₀ : ((AdjoinRoot (poly p))[X] ⧸ Ideal.span {poly q.1.2}) →+*
        (k[X] ⧸ Ideal.span {poly h}) :=
      (AdjoinRoot.towerFactorRingEquiv (poly p) (poly h) f).toRingHom
    let σ : (k[X] ⧸ Ideal.span {poly h}) →+*
        (K[X] ⧸ Ideal.span {poly s.1.2}) :=
      AdjoinRoot.map φ (poly h) (poly s.1.2) s.2
    simpleMilnorNorm r (simpleMilnorNorm t (milnorKRingMap ρ x)) =
      simpleMilnorNorm s.1.2 (milnorKRingMap σ (milnorKRingMap θ₀ x)) := by
  exact simpleMilnorNorm_nestedScalarFactor_pGroup_square_of_isGalois φ p h f s ℓ hG j x

end
