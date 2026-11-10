/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Norm.DVRComplete

/-! Full-statement consumers for the complete-DVR source migration. -/

noncomputable section

open Stacks.Chow Polynomial Stacks.Chow.MonicIrreducibleOfDegree AdjoinRoot IsLocalRing
open IsDiscreteValuationRing.CompleteExtension

attribute [local instance] Ideal.Quotient.field
attribute [local instance] AdjoinRoot.instFactIrreduciblePolynomialPoly_colib

universe u

variable (R F E S : Type u)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsAdicComplete (maximalIdeal R) R] [CharZero (ResidueField R)]
  [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Field E] [Algebra F E] [FiniteDimensional F E]
  [Algebra R E] [IsScalarTower R F E]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [IsLocalHom (algebraMap R S)]
  [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
  [IsIntegralClosure S R E]

example (n : ℕ) (x : MilnorKTheory E (n + 1)) :
    dvrMilnorTameSymbol' R F n (milnorKNorm F E (n + 1) x) =
      milnorKNorm (ResidueField R) (ResidueField S) n
        (dvrMilnorTameSymbol' S E n x) := by
  exact dvrMilnorTameSymbol'_milnorKNorm_complete R F E S n x

example (n : ℕ) :
    (dvrMilnorTameSymbol' R F n).comp (milnorKNorm F E (n + 1)) =
      (milnorKNorm (ResidueField R) (ResidueField S) n).comp
        (dvrMilnorTameSymbol' S E n) := by
  exact dvrMilnorTameSymbol'_comp_milnorKNorm_complete R F E S n

example (x : MilnorKTheory E 1) :
    dvrMilnorTameSymbol' R F 0 (milnorKNorm F E 1 x) =
      milnorKNorm (ResidueField R) (ResidueField S) 0
        (dvrMilnorTameSymbol' S E 0 x) := by
  exact dvrMilnorTameSymbol'_milnorKNorm_complete R F E S 0 x

end
