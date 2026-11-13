/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.DiscreteValuationRing.CompleteExtension
public import Colib.RingTheory.IntegralClosure.JapaneseDVR
public import StacksFrontier.RingTheory.DiscreteValuationRing.RamificationIndex
public import StacksFrontier.RingTheory.Nagata.CompleteLocalRing

/-!
# Normalizations of complete DVRs in finite field extensions

The Nagata property supplies finiteness of the actual integral closure
in any finite extension. Its locality and Dedekind property give a DVR.
The extended ideal is a positive power of the new maximal ideal, so
completeness of the finite algebra gives completeness of the normalization.
-/

@[expose] public noncomputable section

open IsLocalRing Stacks.DiscreteValuationRing.Ramification

namespace IsDiscreteValuationRing.CompleteExtension

private theorem isJapaneseRing_of_completeDVR
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (maximalIdeal R) R] : IsJapaneseRing R :=
  MonogenicN1.isJapaneseRing_of_isNagataRing IsNagataRing.of_isPrecomplete_maximalIdeal

variable (R K L : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsAdicComplete (maximalIdeal R) R] [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L] [FiniteDimensional K L]

include K

/-- The integral closure of a complete DVR is finite in every finite field extension. -/
theorem integralClosure_finite_of_finite : Module.Finite R (integralClosure R L) :=
  module_finite_integralClosure_of_isJapaneseRing (isJapaneseRing_of_completeDVR R) K L

/-- The finite normalization of a complete DVR is local. -/
theorem integralClosure_isLocalRing_of_finite : IsLocalRing (integralClosure R L) := by
  let : Module.Finite R (integralClosure R L) := integralClosure_finite_of_finite R K L
  exact isLocalRing_of_finite R (integralClosure R L)

/-- The normalization is a DVR in every finite extension of the fraction field. -/
theorem integralClosure_isDiscreteValuationRing_of_finite :
    IsDiscreteValuationRing (integralClosure R L) := by
  let : IsLocalRing (integralClosure R L) := integralClosure_isLocalRing_of_finite R K L
  let : IsDedekindDomain (integralClosure R L) :=
    isDedekindDomain_integralClosure_of_isJapaneseRing R (isJapaneseRing_of_completeDVR R) K L
  have hnf : ¬ IsField (integralClosure R L) := fun h =>
    IsDiscreteValuationRing.not_isField R
      (isField_of_isIntegral_of_isField (integralClosure_algebraMap_injective R K L) h)
  exact ((IsDiscreteValuationRing.TFAE (integralClosure R L) hnf).out 1 3).mpr
    (show IsDedekindDomain (integralClosure R L) from inferInstance)

/-- The actual integral closure is complete for its maximal ideal. -/
theorem integralClosure_isAdicComplete_of_finite :
    let _ := integralClosure_isLocalRing_of_finite R K L
    IsAdicComplete (maximalIdeal (integralClosure R L)) (integralClosure R L) := by
  let A := integralClosure R L
  let : IsDiscreteValuationRing A := integralClosure_isDiscreteValuationRing_of_finite R K L
  let : Module.Finite R A := integralClosure_finite_of_finite R K L
  let : IsLocalHom (algebraMap R A) := integralClosure_isLocalHom R K L
  let : FaithfulSMul R A :=
    (faithfulSMul_iff_algebraMap_injective R A).mpr (integralClosure_algebraMap_injective R K L)
  have hcomplete : IsAdicComplete ((maximalIdeal R).map (algebraMap R A)) A :=
    IsAdicComplete.map_algebraMap_of_finite R _ A
  rw [map_maximalIdeal_eq_maximalIdeal_pow_ramificationIdx R A] at hcomplete
  let _ := hcomplete
  exact isAdicComplete_of_pow A (maximalIdeal A) (ramificationIdx R A)
    (one_le_ramificationIdx R A)

/-- The residue extension of the finite normalization is finite. -/
theorem integralClosure_residue_finite_of_finite :
    let _ := integralClosure_isLocalRing_of_finite R K L
    let _ := integralClosure_isLocalHom R K L
    Module.Finite (ResidueField R) (ResidueField (integralClosure R L)) := by
  let _ := integralClosure_isLocalRing_of_finite R K L
  let _ := integralClosure_isLocalHom R K L
  let : Module.Finite R (integralClosure R L) := integralClosure_finite_of_finite R K L
  exact IsLocalRing.ResidueField.finite_of_module_finite

end IsDiscreteValuationRing.CompleteExtension

end
