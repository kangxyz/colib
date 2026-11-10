/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Norm.DVRCompletePGroupDescent

/-! Full-statement consumers for the complete-DVR source migration. -/

noncomputable section

open Stacks.Chow Polynomial Stacks.Chow.MonicIrreducibleOfDegree AdjoinRoot IsLocalRing
open IsDiscreteValuationRing.CompleteExtension

attribute [local instance] Ideal.Quotient.field
attribute [local instance] AdjoinRoot.instFactIrreduciblePolynomialPoly_colib

universe u

example
    (R F L : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (maximalIdeal R) R] [CharZero (ResidueField R)]
    [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
    [Field L] [Algebra F L] [FiniteDimensional F L]
    [Algebra R L] [IsScalarTower R F L]
    {d : ℕ} (p : MonicIrreducibleOfDegree F d)
    (Ω : Type u) [Field Ω] [Algebra L Ω] [FiniteDimensional L Ω] [IsGalois L Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] (hG : IsPGroup ℓ (Ω ≃ₐ[L] Ω))
    (g : ∀ r : {r : Σ e : ℕ, MonicIrreducibleOfDegree L e //
      poly r.2 ∣ (poly p).map (algebraMap F L)}, AdjoinRoot (poly r.1.2) →ₐ[L] Ω)
    (n : ℕ) (x : MilnorKTheory (AdjoinRoot (poly p)) (n + 1)) :
    let _ := (AdjoinRoot.powerBasis' (monic p)).finite
    let _ := integralClosure_isDiscreteValuationRing R F (AdjoinRoot (poly p))
    let _ := integralClosure_isLocalHom R F (AdjoinRoot (poly p))
    let _ := IsIntegralClosure.isFractionRing_of_finite_extension R F (AdjoinRoot (poly p))
      (integralClosure R (AdjoinRoot (poly p)))
    let _ := integralClosure_residue_finite R F (AdjoinRoot (poly p))
    Module.finrank F L •
      (dvrMilnorTameSymbol' R F n (milnorKNorm F (AdjoinRoot (poly p)) (n + 1) x) -
        milnorKNorm (ResidueField R)
          (ResidueField (integralClosure R (AdjoinRoot (poly p)))) n
          (dvrMilnorTameSymbol' (integralClosure R (AdjoinRoot (poly p)))
            (AdjoinRoot (poly p)) n x)) = 0 := by
  exact finrank_smul_norm_residue_difference_complete_of_pGroup_branches R F L p Ω ℓ hG g n x

end
