/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.AdjoinRoot.NestedScalarFactorQuotient
public import Colib.RingTheory.KTheory.MilnorK.Norm.BranchFactorTransport

/-!
# A native p-group tower through an actual relative quotient comparison

Only polynomial identity and literal quotient-map compatibility are inputs.
There is no norm comparison hypothesis and no selected scalar-factor index.
-/

@[expose] public noncomputable section

open Polynomial

universe u v

namespace Stacks.Chow

open MonicIrreducibleOfDegree
attribute [local instance] Ideal.Quotient.field
attribute [local instance] AdjoinRoot.instFactIrreduciblePolynomialPoly_colib

variable {K : Type u} [Field K] [CharZero K]
  {Ω : Type v} [Field Ω] [Algebra K Ω] [FiniteDimensional K Ω] [IsGalois K Ω]

/-- Algebraic comparison with the canonical relative quotient suffices for the native norm tower. -/
theorem simpleMilnorNorm_pGroup_tower_of_native_factor_comparison
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
    (j : AdjoinRoot (poly s) →ₐ[K] Ω) (y : MilnorKRing (AdjoinRoot (poly t))) :
    simpleMilnorNorm r (simpleMilnorNorm t y) =
      simpleMilnorNorm s (milnorKRingMap ε.toRingHom y) := by
  exact simpleMilnorNorm_pGroup_tower_of_quotient_comparison
    r s i t c ε hpoly hc hcomp ℓ hG j y

end Stacks.Chow
end
