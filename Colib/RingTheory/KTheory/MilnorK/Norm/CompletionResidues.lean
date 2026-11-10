/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Residue.Completion
public import Colib.RingTheory.KTheory.MilnorK.Norm.ChosenEquivariance

/-!
# Chosen norms on the actual completion residue fields

The original scalar tower gives the residue-field square. The equivalences here are
exactly the inverses of the actual bijective residue maps used by the native completion
comparison. No replacement completion, residue field or norm is defined.

Adapted from `Aglib/KTheory/MilnorK/Norm/FiniteExtension/CompletionResidues.lean`
at revision `4f65be4eafa8964bd1f7a83682e99aa8165bd418`, lines 33–70.
The characteristic-zero residue hypothesis and the literal completed algebra action
are retained. The resulting norm square uses the native chosen norm in every degree.
-/

@[expose] public noncomputable section

namespace Stacks.Chow

open IsLocalRing

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

/-- The inverse actual completion residue maps preserve the original algebra square. -/
theorem dvrCompletionResidueEquiv_algebraMap (a : ResidueField CR) :
    (eS).symm (algebraMap (ResidueField CR) (ResidueField CS) a) =
      algebraMap (ResidueField R) (ResidueField S) ((eR).symm a) := by
  obtain ⟨b, rfl⟩ := (AdicCompletion.residueField_map_bijective R).2 a
  change (eS).symm
      (algebraMap (ResidueField CR) (ResidueField CS) (eR b)) =
    algebraMap (ResidueField R) (ResidueField S) ((eR).symm (eR b))
  rw [(eR).symm_apply_apply]
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective b
  change (eS).symm (IsLocalRing.residue CS
      (algebraMap CR CS (algebraMap R CR r))) =
    IsLocalRing.residue S (algebraMap R S r)
  rw [← IsScalarTower.algebraMap_apply R CR CS,
    IsScalarTower.algebraMap_apply R S CS]
  exact (eS).symm_apply_apply (IsLocalRing.residue S (algebraMap R S r))

/-- The native chosen residue norm commutes with the actual completion identifications. -/
theorem milnorKNorm_completionResidueEquiv
    [CharZero (ResidueField R)]
    [FiniteDimensional (ResidueField R) (ResidueField S)]
    [FiniteDimensional (ResidueField CR) (ResidueField CS)]
    (n : ℕ) (x : MilnorKTheory (ResidueField CS) n) :
    milnorKTransport (eR).symm.toRingHom n
      (milnorKNorm (ResidueField CR) (ResidueField CS) n x) =
      milnorKNorm (ResidueField R) (ResidueField S) n
        (milnorKTransport (eS).symm.toRingHom n x) := by
  have : CharZero (ResidueField CR) := (eR).symm.toRingHom.charZero
  exact milnorKNorm_map_ringEquiv (eR).symm (eS).symm
    (RingHom.ext (dvrCompletionResidueEquiv_algebraMap R S)) n x

end Stacks.Chow

end
