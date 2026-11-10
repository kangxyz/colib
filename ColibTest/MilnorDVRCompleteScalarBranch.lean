/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Norm.DVRCompleteScalarBranch

noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree AdjoinRoot IsLocalRing

universe u v

attribute [local instance] Ideal.Quotient.field
attribute [local instance] AdjoinRoot.instFactIrreduciblePolynomialPoly_colib

open IsDiscreteValuationRing.CompleteExtension IsDiscreteValuationRing.IntegralClosureTower
open Stacks.Chow.CompleteScalarBranch

attribute [local instance] AdjoinRoot.scalarBranchAlgebra closureAlgebra

variable (R F L : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsAdicComplete (maximalIdeal R) R] [CharZero (ResidueField R)]
  [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Field L] [Algebra F L] [Algebra R L] [IsScalarTower R F L] [FiniteDimensional F L]
  {d : ℕ} (p : MonicIrreducibleOfDegree F d)
  (r : {r : Σ e : ℕ, MonicIrreducibleOfDegree L e //
    poly r.2 ∣ (poly p).map (algebraMap F L)})

example
    (Ω : Type u) [Field Ω] [Algebra L Ω] [FiniteDimensional L Ω] [IsGalois L Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] (hG : IsPGroup ℓ (Ω ≃ₐ[L] Ω))
    (g : AdjoinRoot (poly r.1.2) →ₐ[L] Ω) (n : ℕ)
    (x : MilnorKTheory (AdjoinRoot (poly r.1.2)) (n + 1)) :
    let _ : CharZero L := charZero_of_injective_algebraMap (algebraMap F L).injective
    let _ : FiniteDimensional L (AdjoinRoot (poly r.1.2)) :=
      (AdjoinRoot.powerBasis' (monic r.1.2)).finite
    let _ : FiniteDimensional F (AdjoinRoot (poly r.1.2)) := Module.Finite.trans L _
    let _ := integralClosure_isDiscreteValuationRing R F L
    let _ := integralClosure_isDiscreteValuationRing R F (AdjoinRoot (poly r.1.2))
    let _ := integralClosure_isLocalHom R F L
    let _ := coefficient_isLocalHom R p r
    let _ := IsIntegralClosure.isFractionRing_of_finite_extension R F L (integralClosure R L)
    let _ := IsIntegralClosure.isFractionRing_of_finite_extension R F (AdjoinRoot (poly r.1.2))
      (integralClosure R (AdjoinRoot (poly r.1.2)))
    let _ := coefficient_finite R F L p r
    let _ : CharZero (ResidueField (integralClosure R L)) :=
      charZero_of_injective_algebraMap
        (algebraMap (ResidueField R) (ResidueField (integralClosure R L))).injective
    dvrMilnorTameSymbol' (integralClosure R L) L n
        (milnorKNorm L (AdjoinRoot (poly r.1.2)) (n + 1) x) =
      milnorKNorm (ResidueField (integralClosure R L))
        (ResidueField (integralClosure R (AdjoinRoot (poly r.1.2)))) n
        (dvrMilnorTameSymbol' (integralClosure R (AdjoinRoot (poly r.1.2)))
          (AdjoinRoot (poly r.1.2)) n x) :=
  dvrMilnorTameSymbol'_milnorKNorm_complete_scalarBranch_of_pGroup R F L p r Ω ℓ hG g n x

end
