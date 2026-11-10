/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Norm.CompletionResidues

/-! Actual native completed-residue norm consumer with the original scalar tower. -/

noncomputable section

open Stacks.Chow IsLocalRing

universe u

attribute [local instance] dvrCompletion_isDomain dvrCompletion_isDiscreteValuationRing

variable (R S : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [IsLocalHom (algebraMap R S)]
  [Algebra (AdicCompletion (maximalIdeal R) R) (AdicCompletion (maximalIdeal S) S)]
  [IsLocalHom (algebraMap (AdicCompletion (maximalIdeal R) R)
    (AdicCompletion (maximalIdeal S) S))]
  [IsScalarTower R (AdicCompletion (maximalIdeal R) R) (AdicCompletion (maximalIdeal S) S)]

local notation "CR" => AdicCompletion (maximalIdeal R) R
local notation "CS" => AdicCompletion (maximalIdeal S) S
local notation "eR" => RingEquiv.ofBijective
  (ResidueField.map (algebraMap R CR)) (AdicCompletion.residueField_map_bijective R)
local notation "eS" => RingEquiv.ofBijective
  (ResidueField.map (algebraMap S CS)) (AdicCompletion.residueField_map_bijective S)

example
    [CharZero (ResidueField R)]
    [FiniteDimensional (ResidueField R) (ResidueField S)]
    [FiniteDimensional (ResidueField CR) (ResidueField CS)]
    (n : ℕ) (x : MilnorKTheory (ResidueField CS) n) :
    milnorKTransport (eR).symm.toRingHom n
      (milnorKNorm (ResidueField CR) (ResidueField CS) n x) =
      milnorKNorm (ResidueField R) (ResidueField S) n
        (milnorKTransport (eS).symm.toRingHom n x) := by
  exact milnorKNorm_completionResidueEquiv R S n x

end
