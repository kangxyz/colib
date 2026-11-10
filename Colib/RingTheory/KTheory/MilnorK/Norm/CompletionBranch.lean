/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.CompletionResidues
public import Colib.RingTheory.KTheory.MilnorK.Norm.DVRComplete

/-!
# The actual completed norm on one original DVR branch

The general complete-DVR norm square and the actual residue identifications yield
the branch formula. The completed algebra, original fraction field and canonical
fraction lift are retained. No norm compatibility premise is assumed.

Adapted from `Aglib/KTheory/MilnorK/Norm/FiniteExtension/CompletionBranch.lean`
at revision `4f65be4eafa8964bd1f7a83682e99aa8165bd418`, lines 44–74.
-/

@[expose] public noncomputable section

namespace Stacks.Chow

open IsLocalRing

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

/-- The norm on the actual completed fraction fields computes the original branch residue. -/
theorem dvrMilnorTameSymbol_completed_norm_eq_original_branch
    (n : ℕ) (x : MilnorKTheory E (n + 1)) :
    milnorKTransport (eR).symm.toRingHom n
      (dvrMilnorTameSymbol' CR QR n
        (milnorKNorm QR QS (n + 1) (milnorKTheoryMap φS (n + 1) x))) =
      milnorKNorm (ResidueField R) (ResidueField S) n
        (dvrMilnorTameSymbol' S E n x) := by
  have : CharZero (ResidueField CR) := (eR).symm.toRingHom.charZero
  have : CharZero CR := (IsLocalRing.residue CR).charZero
  have : CharZero QR := charZero_of_injective_algebraMap (IsFractionRing.injective CR QR)
  rw [dvrMilnorTameSymbol'_milnorKNorm_complete CR QR QS CS,
    milnorKNorm_completionResidueEquiv R S]
  have hc := dvrMilnorTameSymbol'_completion_identification S E n x
  dsimp only at hc
  have hc' : milnorKTransport (eS).symm.toRingHom n
      (dvrMilnorTameSymbol' CS QS n (milnorKTheoryMap φS (n + 1) x)) =
      dvrMilnorTameSymbol' S E n x := by
    simpa only [milnorKTheoryMap_eq_transport, AddMonoidHom.coe_toIntLinearMap] using hc
  exact congrArg (milnorKNorm (ResidueField R) (ResidueField S) n) hc'

end Stacks.Chow

end
