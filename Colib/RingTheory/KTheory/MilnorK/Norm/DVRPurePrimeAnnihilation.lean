/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.DiscreteValuationRing.RamificationDegree
public import Colib.RingTheory.KTheory.MilnorK.Norm.ChosenInseparableTrace
public import Colib.RingTheory.KTheory.MilnorK.Residue.CanonicalRamifiedMap
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Degree annihilation of the purely inseparable norm-residue error

Pure inseparability descends from the actual fraction fields to the actual
residue fields. A residue representative has a suitable characteristic power
in the lower fraction field; its integrality descends that power to the lower
DVR before reduction.

The two native restriction-after-norm identities and ramified tame-symbol
functoriality show that the ramification index kills the restricted error.
Applying the native residue norm and the local degree formula shows that the
fraction-field degree kills the original error. This includes prime degree,
but neither primeness nor cancellation of a Milnor-group scalar is needed.
The independent coprime annihilator and the all-symbol equality remain separate.
-/

@[expose] public noncomputable section

open IsLocalRing Module

universe u v

namespace Stacks.Chow

variable (R S : Type u) (F E : Type v)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
  [IsLocalHom (algebraMap R S)]
  [Field F] [Algebra R F] [IsFractionRing R F]
  [Field E] [Algebra F E] [Algebra R E] [IsScalarTower R F E]
  [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
  [IsPurelyInseparable F E]

include F E in
omit [Module.IsTorsionFree R S] in
/-- Pure inseparability of the fraction-field extension descends to the native
residue fields through integrality, including the characteristic-zero case. -/
theorem dvr_residueField_isPurelyInseparable :
    IsPurelyInseparable (ResidueField R) (ResidueField S) := by
  let q := ringExpChar F
  have hpow (y : ResidueField S) :
      ∃ n : ℕ, y ^ q ^ n ∈ (algebraMap (ResidueField R) (ResidueField S)).range := by
    obtain ⟨b, rfl⟩ := residue_surjective y
    obtain ⟨n, a, ha⟩ := IsPurelyInseparable.pow_mem F q (algebraMap S E b)
    have hb : IsIntegral R (algebraMap S E b) :=
      (Algebra.IsIntegral.isIntegral (R := R) b).map (IsScalarTower.toAlgHom R S E)
    have haE : IsIntegral R (algebraMap F E a) := by
      rw [ha]
      exact hb.pow _
    have haR : IsIntegral R a := haE.tower_bot (algebraMap F E).injective
    obtain ⟨a₀, ha₀⟩ := IsIntegrallyClosed.isIntegral_iff.mp haR
    have hS : algebraMap R S a₀ = b ^ q ^ n := by
      apply IsFractionRing.injective S E
      rw [map_pow, ← IsScalarTower.algebraMap_apply R S E,
        IsScalarTower.algebraMap_apply R F E, ha₀]
      exact ha
    refine ⟨n, residue R a₀, ?_⟩
    rw [ResidueField.algebraMap_residue, hS, map_pow]
  rcases expChar_is_prime_or_one F q with hprime | hq
  · let : CharP F q := (expChar_prime_iff F hprime).mp inferInstance
    let : CharP R q := (algebraMap R F).charP (IsFractionRing.injective R F) q
    let : CharP (ResidueField R) q := (CharP.charP_iff_prime_eq_zero hprime).mpr (by
      have h := congrArg (residue R) (CharP.cast_eq_zero R q)
      simpa only [map_natCast, map_zero] using h)
    let : ExpChar (ResidueField R) q :=
      (expChar_prime_iff (ResidueField R) hprime).mpr inferInstance
    exact (isPurelyInseparable_iff_pow_mem (ResidueField R) q).mpr hpow
  · apply (isPurelyInseparable_iff_pow_mem
      (ResidueField R) (ringExpChar (ResidueField R))).mpr
    intro y
    obtain ⟨n, hn⟩ := hpow y
    refine ⟨0, ?_⟩
    simpa only [hq, one_pow, pow_one, pow_zero] using hn

variable [FiniteDimensional F E]

/-- Ramification kills the restricted native norm-residue error for every
finite purely inseparable fraction-field extension. No scalar is cancelled. -/
theorem ramification_smul_restrict_norm_residue_difference_eq_zero_of_isPurelyInseparable
    (n : ℕ) (x : MilnorKTheory E (n + 1)) :
    (Stacks.DiscreteValuationRing.Ramification.ramificationIdx R S : ℤ) •
      milnorKTheoryMap (algebraMap (ResidueField R) (ResidueField S)) n
        (dvrMilnorTameSymbol' R F n (milnorKNorm F E (n + 1) x) -
          milnorKNorm (ResidueField R) (ResidueField S) n
            (dvrMilnorTameSymbol' S E n x)) = 0 := by
  let : IsPurelyInseparable (ResidueField R) (ResidueField S) :=
    dvr_residueField_isPurelyInseparable R S F E
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨ρ, hρ⟩ := IsDiscreteValuationRing.exists_irreducible S
  have hn : algebraMap R S π ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R S)).mpr hπ.ne_zero
  obtain ⟨e, u, he⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hn hρ
  have heidx : e = Stacks.DiscreteValuationRing.Ramification.ramificationIdx R S := by
    have h := Stacks.DiscreteValuationRing.Ramification.addVal_algebraMap_eq_ramificationIdx
      R S π hπ
    rw [he, IsDiscreteValuationRing.addVal_def' u hρ e] at h
    exact_mod_cast h
  have hf : ∀ a : R, algebraMap F E (algebraMap R F a) =
      algebraMap S E (algebraMap R S a) := fun a =>
    (IsScalarTower.algebraMap_apply R F E a).symm.trans
      (IsScalarTower.algebraMap_apply R S E a)
  have hr := DFunLike.congr_fun
    (dvrMilnorTameSymbol'_map_ramified (algebraMap R S) (algebraMap F E) hf
      hπ hρ u e he n) (milnorKNorm F E (n + 1) x)
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.smul_apply, heidx] at hr
  have hd : Stacks.DiscreteValuationRing.Ramification.ramificationIdx R S *
      finrank (ResidueField R) (ResidueField S) = finrank F E := by
    have h := IsDiscreteValuationRing.finrank_eq_ramification_mul_residue_finrank
      R S F E hπ hρ u e he
    simpa only [heidx] using h.symm
  rw [map_sub, smul_sub]
  apply sub_eq_zero.mpr
  calc
    _ = dvrMilnorTameSymbol' S E n
        (milnorKTheoryMap (algebraMap F E) (n + 1)
          (milnorKNorm F E (n + 1) x)) := hr.symm
    _ = (finrank F E : ℤ) • dvrMilnorTameSymbol' S E n x := by
      rw [milnorKTheoryMap_milnorKNorm_of_isPurelyInseparable, map_zsmul]
    _ = _ := by
      rw [milnorKTheoryMap_milnorKNorm_of_isPurelyInseparable,
        smul_smul, ← Nat.cast_mul, hd]

/-- The actual generic degree annihilates every native norm-residue error.
For pure prime degree this is the first annihilator in the coprime descent. -/
theorem finrank_smul_norm_residue_difference_eq_zero_of_isPurelyInseparable
    (n : ℕ) (x : MilnorKTheory E (n + 1)) :
    (finrank F E : ℤ) •
      (dvrMilnorTameSymbol' R F n (milnorKNorm F E (n + 1) x) -
        milnorKNorm (ResidueField R) (ResidueField S) n
          (dvrMilnorTameSymbol' S E n x)) = 0 := by
  let δ : MilnorKTheory (ResidueField R) n :=
    dvrMilnorTameSymbol' R F n (milnorKNorm F E (n + 1) x) -
      milnorKNorm (ResidueField R) (ResidueField S) n
        (dvrMilnorTameSymbol' S E n x)
  have hweighted :=
    ramification_smul_restrict_norm_residue_difference_eq_zero_of_isPurelyInseparable
      R S F E n x
  change (Stacks.DiscreteValuationRing.Ramification.ramificationIdx R S : ℤ) •
    milnorKTheoryMap (algebraMap (ResidueField R) (ResidueField S)) n δ = 0 at hweighted
  have hring : (Stacks.DiscreteValuationRing.Ramification.ramificationIdx R S : ℤ) •
      milnorKRingMap (algebraMap (ResidueField R) (ResidueField S))
        (δ : MilnorKRing (ResidueField R)) = 0 := by
    have h := congrArg ((milnorKGrading (ResidueField S) n).subtype) hweighted
    simpa only [map_zsmul, map_zero, milnorKTheoryMap_eq_transport,
      AddMonoidHom.coe_toIntLinearMap, AddSubgroup.subtype_apply, milnorKTransport_coe] using h
  have hnorm := congrArg (milnorKNormRing (ResidueField R) (ResidueField S)) hring
  rw [map_zsmul, milnorKNormRing_milnorKRingMap, map_zero, smul_smul] at hnorm
  let : FaithfulSMul R S := inferInstance
  let : Module.Flat R S := inferInstance
  have hd : Stacks.DiscreteValuationRing.Ramification.ramificationIdx R S *
      finrank (ResidueField R) (ResidueField S) = finrank F E := by
    have h := Stacks.DiscreteValuationRing.Ramification.ramificationIdx_mul_inertiaDeg_eq_finrank
      R S F E
    rw [Ideal.inertiaDeg_eq_of_isMaximal (p := maximalIdeal R)] at h
    exact h
  rw [← Nat.cast_mul, hd] at hnorm
  apply Subtype.ext
  exact hnorm

end Stacks.Chow

end
