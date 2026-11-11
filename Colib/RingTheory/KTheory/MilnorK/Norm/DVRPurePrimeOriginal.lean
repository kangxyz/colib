/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.DVRPurePrimeComplete
public import Colib.RingTheory.KTheory.MilnorK.Norm.PurePrimeCompletedField
public import Colib.RingTheory.KTheory.MilnorK.Norm.PurePrimeCompletionResidues

import Colib.RingTheory.KTheory.MilnorK.Norm.PurePrimeResidueEquiv

/-!
# The original branch of a purely inseparable prime DVR extension

Complete the given lower DVR and the sole original upper branch. The
native fraction-tensor equivalence identifies the original scalar maps.
The norm square over the complete DVR descends through the two actual
residue maps.
-/

@[expose] public noncomputable section

open IsLocalRing Module _root_.AdicCompletion
open Stacks.DiscreteValuationRing.Ramification
open scoped TensorProduct

universe u

namespace Stacks.Chow

variable (R S F E : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDedekindDomain S] [Algebra R S]
  [Module.Finite R S] [Module.IsTorsionFree R S] [DecidableEq (Ideal S)]
  [Field F] [Algebra R F] [IsFractionRing R F]
  [Field E] [Algebra R E] [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
  [Algebra F E] [IsScalarTower R F E] [FiniteDimensional F E] [IsPurelyInseparable F E]

local notation "J" => Ideal.map (algebraMap R S) (maximalIdeal R)
local notation "CR" => AdicCompletion (maximalIdeal R) R
local notation "QR" => FractionRing CR
local notation "eR" => RingEquiv.ofBijective
  (ResidueField.map (algebraMap R CR)) (AdicCompletion.residueField_map_bijective R)

/-- The native norm-residue square for the original local branch in purely
inseparable prime degree. The original lower DVR may be incomplete. -/
theorem dvrMilnorTameSymbol'_milnorKNorm_eq_originalBranch_of_isPurelyInseparable_of_prime
    (q : IdealBranch J) (hp : Nat.Prime (finrank F E)) (n : ℕ) (x : MilnorKTheory E (n + 1)) :
    letI := originalBranchFractionAlgebra S E q
    letI := originalBranchIsFractionRing S E q
    dvrMilnorTameSymbol' R F n (milnorKNorm F E (n + 1) x) =
      milnorKNorm (ResidueField R) (ResidueField (Localization.AtPrime q.val)) n
        (dvrMilnorTameSymbol' (Localization.AtPrime q.val) E n x) := by
  let : q.val.IsMaximal := idealBranchIsMaximal J q
  let : q.val.IsPrime := inferInstance
  let T := Localization.AtPrime q.val
  let : IsDiscreteValuationRing T := idealBranchLocalizationIsDiscreteValuationRing J q
  let D := BranchCompletion J q
  let Q := FractionRing D
  let := originalBranchFractionAlgebra S E q
  let := originalBranchIsFractionRing S E q
  let := originalBranchFractionTower S E q
  let := fractionCompletionAlgebra R F
  let := fractionCompletionIsScalarTower R F
  let := localCompletionBaseAlgebra (maximalIdeal R) q
  let := localCompletionBaseIsScalarTower (maximalIdeal R) q
  let := localCompletionBase_isLocalHom R S q
  let := localCompletionBaseFaithfulSMul R S q
  let := localCompletionBaseFinite (maximalIdeal R) (map_maximalIdeal_ne_zero R S) q
  let := localCompletionFractionAlgebra R S q
  let := localCompletionFractionIsScalarTower R S q
  let := localCompletionFractionFinite R S q
  let η : QR ⊗[F] E ≃ₐ[QR] Q := fractionTensorEquivPurelyInseparableBranch R S F E q
  let : Algebra E Q := fractionCompletionAlgebra (Localization.AtPrime q.val) E
  have hφ : η.toRingHom.comp
      (Algebra.TensorProduct.includeRight : E →ₐ[F] QR ⊗[F] E).toRingHom = algebraMap E Q :=
    (fractionTensorEquivPurelyInseparableBranch_coordinate R S F E q).trans
      (fractionCompletionAlgebra_algebraMap (Localization.AtPrime q.val) E).symm
  let : Algebra F Q := ((algebraMap QR Q).comp (algebraMap F QR)).toAlgebra
  let : IsScalarTower F QR Q := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower F E Q := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap QR Q (algebraMap F QR a) = algebraMap E Q (algebraMap F E a)
    rw [← RingHom.congr_fun hφ (algebraMap F E a)]
    change _ = η ((Algebra.TensorProduct.includeRight : E →ₐ[F] QR ⊗[F] E)
      (algebraMap F E a))
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply F QR (QR ⊗[F] E), η.commutes]
  let : IsPurelyInseparable QR Q := isPurelyInseparable_of_completedTensorEquiv F E QR Q η
  have hdegree : finrank QR Q = finrank F E :=
    η.toLinearEquiv.finrank_eq.symm.trans Module.finrank_baseChange
  have hbase :
      milnorKTheoryMap (algebraMap F QR) (n + 1) (milnorKNorm F E (n + 1) x) =
      milnorKNorm QR Q (n + 1) (milnorKTheoryMap (algebraMap E Q) (n + 1) x) :=
    milnorKNorm_baseChange_of_prime_of_isPurelyInseparable_of_tensorField F E QR Q η hp (n + 1) x
  let : Module.IsTorsionFree CR D :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (localCompletionBase_injective R S q)
  let : Module.Flat CR D := inferInstance
  let : IsPurelyInseparable (ResidueField CR) (ResidueField D) :=
    dvr_residueField_isPurelyInseparable CR D QR Q
  have hdiv : finrank (ResidueField CR) (ResidueField D) ∣ finrank F E := by
    have h := ramificationIdx_mul_inertiaDeg_eq_finrank CR D QR Q
    rw [Ideal.inertiaDeg_eq_of_isMaximal (p := maximalIdeal CR), hdegree] at h
    exact ⟨ramificationIdx CR D, h.symm.trans (Nat.mul_comm _ _)⟩
  have hscalar : IsFractionRing.lift (A := R) (K := F)
      (g := algebraMap R QR) (dvrCompletionFraction_algebraMap_injective R) =
      algebraMap F QR :=
    dvrCompletionFractionLift_unique R F (algebraMap F QR)
      (fractionCompletionAlgebra_algebraMap_apply R F)
  let A := (milnorKTransport (eR).symm.toRingHom n).comp (dvrMilnorTameSymbol' CR QR n)
  have hR : A (milnorKTheoryMap (algebraMap F QR) (n + 1) (milnorKNorm F E (n + 1) x)) =
      dvrMilnorTameSymbol' R F n (milnorKNorm F E (n + 1) x) := by
    simpa only [A, AddMonoidHom.comp_apply, hscalar, milnorKTheoryMap_eq_transport,
      AddMonoidHom.coe_toIntLinearMap] using
      dvrMilnorTameSymbol'_completion_identification R F n (milnorKNorm F E (n + 1) x)
  let y : MilnorKTheory Q (n + 1) := milnorKTheoryMap (algebraMap E Q) (n + 1) x
  let z : MilnorKTheory (ResidueField D) n := dvrMilnorTameSymbol' D Q n y
  have hcomplete : dvrMilnorTameSymbol' CR QR n (milnorKNorm QR Q (n + 1) y) =
      milnorKNorm (ResidueField CR) (ResidueField D) n z :=
    dvrMilnorTameSymbol'_milnorKNorm_of_complete_of_isPurelyInseparable_of_prime
      CR D QR Q (hdegree.symm ▸ hp) n y
  have hnormResidue := milnorKNorm_completionResidueEquiv_of_isPurelyInseparable_of_dvd_prime
    R (Localization.AtPrime q.val) hp hdiv n z
  have hT := dvrMilnorTameSymbol'_completion_identification (Localization.AtPrime q.val) E n x
  have hTscalar := dvrCompletionFractionLift_unique (Localization.AtPrime q.val) E (algebraMap E Q)
    (fractionCompletionAlgebra_algebraMap_apply (Localization.AtPrime q.val) E)
  dsimp only at hT
  have hTtransport := (by
    simpa only [z, y, hTscalar, milnorKTheoryMap_eq_transport, AddMonoidHom.coe_toIntLinearMap]
      using hT : milnorKTransport (RingEquiv.ofBijective (ResidueField.map (algebraMap T D))
        (AdicCompletion.residueField_map_bijective T)).symm.toRingHom n z =
      dvrMilnorTameSymbol' T E n x)
  exact hR.symm.trans ((congrArg A hbase).trans
    ((congrArg (milnorKTransport (eR).symm.toRingHom n) hcomplete).trans
      (hnormResidue.trans (congrArg
        (milnorKNorm (ResidueField R) (ResidueField T) n) hTtransport))))

/-- The original branch residue extension is purely inseparable and its
degree divides the fraction-field degree. -/
theorem originalBranch_residue_isPurelyInseparable_and_finrank_dvd (q : IdealBranch J) :
    IsPurelyInseparable (ResidueField R) (ResidueField (Localization.AtPrime q.val)) ∧
      finrank (ResidueField R) (ResidueField (Localization.AtPrime q.val)) ∣ finrank F E := by
  let : q.val.IsMaximal := idealBranchIsMaximal J q
  let : q.val.IsPrime := inferInstance
  let T := Localization.AtPrime q.val
  let : IsDiscreteValuationRing T := idealBranchLocalizationIsDiscreteValuationRing J q
  let D := BranchCompletion J q
  let Q := FractionRing D
  let := fractionCompletionAlgebra R F
  let := fractionCompletionIsScalarTower R F
  let := localCompletionBaseAlgebra (maximalIdeal R) q
  let := localCompletionBaseIsScalarTower (maximalIdeal R) q
  let := localCompletionBase_isLocalHom R S q
  let := localCompletionBaseFaithfulSMul R S q
  let := localCompletionBaseFinite (maximalIdeal R) (map_maximalIdeal_ne_zero R S) q
  let := localCompletionFractionAlgebra R S q
  let := localCompletionFractionIsScalarTower R S q
  let := localCompletionFractionFinite R S q
  let η : QR ⊗[F] E ≃ₐ[QR] Q := fractionTensorEquivPurelyInseparableBranch R S F E q
  let : IsPurelyInseparable QR Q := isPurelyInseparable_of_completedTensorEquiv F E QR Q η
  let : Module.IsTorsionFree CR D :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (localCompletionBase_injective R S q)
  let : Module.Flat CR D := inferInstance
  let : IsPurelyInseparable (ResidueField CR) (ResidueField D) :=
    dvr_residueField_isPurelyInseparable CR D QR Q
  let σ := (eR).symm
  let τ := (RingEquiv.ofBijective (ResidueField.map (algebraMap T D))
    (AdicCompletion.residueField_map_bijective T)).symm
  have hστ : τ.toRingHom.comp (algebraMap (ResidueField CR) (ResidueField D)) =
      (algebraMap (ResidueField R) (ResidueField T)).comp σ.toRingHom :=
    RingHom.ext (dvrCompletionResidueEquiv_algebraMap R T)
  have hdegree : finrank QR Q = finrank F E :=
    η.toLinearEquiv.finrank_eq.symm.trans Module.finrank_baseChange
  have hdiv : finrank (ResidueField CR) (ResidueField D) ∣ finrank F E := by
    have h := ramificationIdx_mul_inertiaDeg_eq_finrank CR D QR Q
    rw [Ideal.inertiaDeg_eq_of_isMaximal (p := maximalIdeal CR), hdegree] at h
    exact ⟨ramificationIdx CR D, h.symm.trans (Nat.mul_comm _ _)⟩
  refine ⟨IsPurelyInseparable.of_equiv_equiv σ τ hστ, ?_⟩
  rw [← Algebra.finrank_eq_of_equiv_equiv σ τ hστ.symm]
  exact hdiv

end Stacks.Chow

end
