/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Norm.DVRCompleteAdjoinRoot

/-! Full-statement consumers for the complete-DVR source migration. -/

noncomputable section

open Stacks.Chow Polynomial Stacks.Chow.MonicIrreducibleOfDegree AdjoinRoot IsLocalRing
open IsDiscreteValuationRing.CompleteExtension

attribute [local instance] Ideal.Quotient.field
attribute [local instance] AdjoinRoot.instFactIrreduciblePolynomialPoly_colib

universe u

example
    (R F : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (maximalIdeal R) R] [CharZero (ResidueField R)]
    [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
    {d : ℕ} (p : MonicIrreducibleOfDegree F d)
    (n : ℕ) (x : MilnorKTheory (AdjoinRoot (poly p)) (n + 1)) :
    let _ := (AdjoinRoot.powerBasis' (monic p)).finite
    let _ := integralClosure_isDiscreteValuationRing R F (AdjoinRoot (poly p))
    let _ := integralClosure_isLocalHom R F (AdjoinRoot (poly p))
    let _ := IsIntegralClosure.isFractionRing_of_finite_extension R F (AdjoinRoot (poly p))
      (integralClosure R (AdjoinRoot (poly p)))
    let _ := integralClosure_residue_finite R F (AdjoinRoot (poly p))
    dvrMilnorTameSymbol' R F n (milnorKNorm F (AdjoinRoot (poly p)) (n + 1) x) =
      milnorKNorm (ResidueField R)
          (ResidueField (integralClosure R (AdjoinRoot (poly p)))) n
          (dvrMilnorTameSymbol' (integralClosure R (AdjoinRoot (poly p)))
            (AdjoinRoot (poly p)) n x) := by
  exact dvrMilnorTameSymbol'_milnorKNorm_complete_adjoinRoot R F p n x

end
