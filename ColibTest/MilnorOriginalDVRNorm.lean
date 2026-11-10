/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Norm.DVR

/-! Full-statement consumers over a genuinely arbitrary base DVR and all original branches. -/

noncomputable section

open Stacks.Chow IsLocalRing _root_.AdicCompletion

universe u

variable (R S F E : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CharZero (ResidueField R)]
  [CommRing S] [IsDedekindDomain S] [Algebra R S] [Module.Finite R S]
  [Module.IsTorsionFree R S] [DecidableEq (Ideal S)]
  [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Field E] [Algebra R E] [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
  [Algebra F E] [IsScalarTower R F E] [FiniteDimensional F E]

local notation "J" => Ideal.map (algebraMap R S) (maximalIdeal R)

example (n : ℕ) (x : MilnorKTheory E (n + 1)) :
    letI := fun q : IdealBranch J => originalBranchFractionAlgebra S E q
    letI := fun q : IdealBranch J => originalBranchIsFractionRing S E q
    dvrMilnorTameSymbol' R F n (milnorKNorm F E (n + 1) x) =
      ∑ q : IdealBranch J,
        milnorKNorm (ResidueField R) (ResidueField (Localization.AtPrime q.val)) n
          (dvrMilnorTameSymbol' (Localization.AtPrime q.val) E n x) :=
  dvrMilnorTameSymbol'_milnorKNorm_eq_sum_originalBranches R S F E n x

example (n : ℕ) :
    letI := fun q : IdealBranch J => originalBranchFractionAlgebra S E q
    letI := fun q : IdealBranch J => originalBranchIsFractionRing S E q
    (dvrMilnorTameSymbol' R F n).comp (milnorKNorm F E (n + 1)) =
      ∑ q : IdealBranch J,
        (milnorKNorm (ResidueField R) (ResidueField (Localization.AtPrime q.val)) n).comp
          (dvrMilnorTameSymbol' (Localization.AtPrime q.val) E n) :=
  dvrMilnorTameSymbol'_comp_milnorKNorm_eq_sum_originalBranches R S F E n

example (x : MilnorKTheory E 1) :
    letI := fun q : IdealBranch J => originalBranchFractionAlgebra S E q
    letI := fun q : IdealBranch J => originalBranchIsFractionRing S E q
    dvrMilnorTameSymbol' R F 0 (milnorKNorm F E 1 x) =
      ∑ q : IdealBranch J,
        milnorKNorm (ResidueField R) (ResidueField (Localization.AtPrime q.val)) 0
          (dvrMilnorTameSymbol' (Localization.AtPrime q.val) E 0 x) :=
  dvrMilnorTameSymbol'_milnorKNorm_eq_sum_originalBranches R S F E 0 x

end
