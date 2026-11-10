/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Norm.CompletionBranch

/-! Full original-branch consumer of the completed chosen norm identity. -/

noncomputable section

open Stacks.Chow IsLocalRing

universe u

attribute [local instance] dvrCompletion_isDomain dvrCompletion_isDiscreteValuationRing

variable (R S E : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CharZero (ResidueField R)]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [IsLocalHom (algebraMap R S)]
  [FiniteDimensional (ResidueField R) (ResidueField S)]
  [Field E] [Algebra S E] [IsFractionRing S E]

local notation "CR" => AdicCompletion (maximalIdeal R) R
local notation "CS" => AdicCompletion (maximalIdeal S) S
local notation "QR" => FractionRing CR
local notation "QS" => FractionRing CS
local notation "eR" => RingEquiv.ofBijective
  (ResidueField.map (algebraMap R CR)) (AdicCompletion.residueField_map_bijective R)
local notation "eS" => RingEquiv.ofBijective
  (ResidueField.map (algebraMap S CS)) (AdicCompletion.residueField_map_bijective S)
local notation "φS" => IsFractionRing.lift (A := S) (K := E)
  (g := algebraMap S QS) (dvrCompletionFraction_algebraMap_injective S)

variable
  [Algebra (AdicCompletion (maximalIdeal R) R) (AdicCompletion (maximalIdeal S) S)]
  [IsLocalHom (algebraMap (AdicCompletion (maximalIdeal R) R)
    (AdicCompletion (maximalIdeal S) S))]
  [Module.Finite (AdicCompletion (maximalIdeal R) R) (AdicCompletion (maximalIdeal S) S)]
  [IsScalarTower R (AdicCompletion (maximalIdeal R) R) (AdicCompletion (maximalIdeal S) S)]
  [Algebra (FractionRing (AdicCompletion (maximalIdeal R) R))
    (FractionRing (AdicCompletion (maximalIdeal S) S))]
  [IsScalarTower (AdicCompletion (maximalIdeal R) R)
    (FractionRing (AdicCompletion (maximalIdeal R) R))
    (FractionRing (AdicCompletion (maximalIdeal S) S))]
  [FiniteDimensional (FractionRing (AdicCompletion (maximalIdeal R) R))
    (FractionRing (AdicCompletion (maximalIdeal S) S))]

example
    (n : ℕ) (x : MilnorKTheory E (n + 1)) :
    milnorKTransport (eR).symm.toRingHom n
      (dvrMilnorTameSymbol' CR QR n
        (milnorKNorm QR QS (n + 1) (milnorKTheoryMap φS (n + 1) x))) =
      milnorKNorm (ResidueField R) (ResidueField S) n
        (dvrMilnorTameSymbol' S E n x) := by
  exact dvrMilnorTameSymbol_completed_norm_eq_original_branch R S E n x

end
