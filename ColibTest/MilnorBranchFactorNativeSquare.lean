module

import Colib.RingTheory.KTheory.MilnorK.Norm.BranchFactorNativeSquare

noncomputable section
open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree
universe u v
attribute [local instance] Ideal.Quotient.field
attribute [local instance] AdjoinRoot.instFactIrreduciblePolynomialPoly_colib

example
    {K : Type u} [Field K] [CharZero K]
    {Ω : Type v} [Field Ω] [Algebra K Ω] [FiniteDimensional K Ω] [IsGalois K Ω]
    {Q H : Type u} [Field Q] [Field H]
    {d e m : ℕ} (r : MonicIrreducibleOfDegree K d) (s : MonicIrreducibleOfDegree K e)
    (i : AdjoinRoot (poly r) →ₐ[K] AdjoinRoot (poly s))
    (t : MonicIrreducibleOfDegree (AdjoinRoot (poly r)) m)
    (c : AdjoinRoot (poly t) ≃+* AdjoinRoot (poly (AdjoinRoot.towerFactor (poly r) (poly s) i).1.2))
    (ε : AdjoinRoot (poly t) ≃+* AdjoinRoot (poly s))
    (hpoly : poly (AdjoinRoot.towerFactor (poly r) (poly s) i).1.2 = (poly t).map (RingHom.id
      (AdjoinRoot (poly r))))
    (hdiv : poly (AdjoinRoot.towerFactor (poly r) (poly s) i).1.2 ∣
      (poly t).map (RingHom.id (AdjoinRoot (poly r))))
    (hc : c.toRingHom = AdjoinRoot.map (RingHom.id (AdjoinRoot (poly r)))
      (poly t) (poly (AdjoinRoot.towerFactor (poly r) (poly s) i).1.2) hdiv)
    (hcomp : (AdjoinRoot.towerFactorRingEquiv (poly r) (poly s) i).toRingHom.comp c.toRingHom =
      ε.toRingHom)
    (ℓ : ℕ) [Fact ℓ.Prime] (hG : IsPGroup ℓ (Ω ≃ₐ[K] Ω))
    (j : AdjoinRoot (poly s) →ₐ[K] Ω)
    (ρ : Q →+* AdjoinRoot (poly t)) (θ₀ : Q →+* H)
    (σ : H →+* AdjoinRoot (poly s))
    (hsquare : ε.toRingHom.comp ρ = σ.comp θ₀) (x : MilnorKRing Q) :
    simpleMilnorNorm r (simpleMilnorNorm t (milnorKRingMap ρ x)) =
      simpleMilnorNorm s (milnorKRingMap σ (milnorKRingMap θ₀ x)) := by
  exact simpleMilnorNorm_pGroup_tower_of_native_factor_square
    r s i t c ε hpoly hdiv hc hcomp ℓ hG j ρ θ₀ σ hsquare x

end
