/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.CompletionResidues

import Colib.RingTheory.KTheory.MilnorK.Norm.PurePrimeResidueEquiv

/-!
# Norm transport on purely inseparable completion residue extensions

The inverse actual completion residue maps preserve the original coefficient
square. When the completed residue degree divides a prime, degree one uses
separable norm equivariance and prime degree uses purely inseparable equivariance.
-/

@[expose] public noncomputable section

open IsLocalRing Module

universe u

namespace Stacks.Chow

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

/-- The native residue norm commutes with the actual completion identifications
for a purely inseparable residue extension of degree dividing a prime. -/
theorem milnorKNorm_completionResidueEquiv_of_isPurelyInseparable_of_dvd_prime
    [FiniteDimensional (ResidueField R) (ResidueField S)]
    [FiniteDimensional (ResidueField CR) (ResidueField CS)]
    [IsPurelyInseparable (ResidueField CR) (ResidueField CS)]
    {p : ℕ} (hp : p.Prime) (hdiv : finrank (ResidueField CR) (ResidueField CS) ∣ p)
    (n : ℕ) (x : MilnorKTheory (ResidueField CS) n) :
    milnorKTransport (eR).symm.toRingHom n
      (milnorKNorm (ResidueField CR) (ResidueField CS) n x) =
      milnorKNorm (ResidueField R) (ResidueField S) n
        (milnorKTransport (eS).symm.toRingHom n x) := by
  let σ := (eR).symm
  let τ := (eS).symm
  have hcoeff (a : ResidueField CR) :
      τ (algebraMap (ResidueField CR) (ResidueField CS) a) =
        algebraMap (ResidueField R) (ResidueField S) (σ a) :=
    dvrCompletionResidueEquiv_algebraMap R S a
  have hστ : τ.toRingHom.comp (algebraMap (ResidueField CR) (ResidueField CS)) =
      (algebraMap (ResidueField R) (ResidueField S)).comp σ.toRingHom := RingHom.ext hcoeff
  exact milnorKNorm_map_ringEquiv_of_isPurelyInseparable_of_dvd_prime hp hdiv σ τ hστ n x

end Stacks.Chow

end
