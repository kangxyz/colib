module

import Colib.RingTheory.KTheory.MilnorK.Norm.BranchFactorNativeTransport

noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree

universe u v

attribute [local instance] Ideal.Quotient.field
attribute [local instance] AdjoinRoot.instFactIrreduciblePolynomialPoly_colib

variable {K : Type u} [Field K] [CharZero K]
  {Ω : Type v} [Field Ω] [Algebra K Ω] [FiniteDimensional K Ω] [IsGalois K Ω]
variable
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

/-- Actual algebraic quotient compatibility yields the original whole-ring norm equation. -/
example (y : MilnorKRing (AdjoinRoot (poly t))) :
    simpleMilnorNorm r (simpleMilnorNorm t y) =
      simpleMilnorNorm s (milnorKRingMap ε.toRingHom y) :=
  simpleMilnorNorm_pGroup_tower_of_native_factor_comparison r s i t c ε hpoly hdiv hc hcomp ℓ hG j y

/-- The same equation is equality of the actual additive maps, not merely generators. -/
example :
    (simpleMilnorNorm r).comp (simpleMilnorNorm t) =
      (simpleMilnorNorm s).comp (milnorKRingMap ε.toRingHom).toAddMonoidHom := by
  ext y
  exact simpleMilnorNorm_pGroup_tower_of_native_factor_comparison r s i t c ε hpoly hdiv hc hcomp ℓ hG j y

end
