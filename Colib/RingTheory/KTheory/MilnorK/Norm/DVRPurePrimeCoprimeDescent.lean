/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.DVRPurePrimeMixed
public import Colib.RingTheory.KTheory.MilnorK.Norm.DVRPurePrimeAnnihilation
public import Colib.RingTheory.KTheory.MilnorK.Norm.PurePrimeCoprimeBaseChange
public import Mathlib.Data.Int.GCD

/-!
# Norm-residue equality for a supplied coprime DVR square

For an actual finite square of DVRs, coprimality of the horizontal field degrees
forces equality of the two vertical ramification indices and residue degrees.
The native chosen-norm base-change theorem applies to the actual fraction and
residue fields. A mixed expansion upstairs therefore kills the restricted
norm-residue error with its actual ramification weight. The residue norm turns
this into the coprime field-degree annihilator, and Bezout gives equality.

The results in the supplied-square section retain the actual rings, fields,
scalar towers, finiteness and mixed membership as explicit inputs. They do not
assert that an auxiliary normalization or a mixed witness has been constructed.
-/

@[expose] public noncomputable section

open IsLocalRing Module
open Stacks.DiscreteValuationRing.Ramification

universe u

namespace Stacks.Chow

private theorem pureComplete_local_degree
    (R S F E : Type u)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
    [IsLocalHom (algebraMap R S)]
    [Field F] [Algebra R F] [IsFractionRing R F]
    [Field E] [Algebra F E] [Algebra R E] [IsScalarTower R F E]
    [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E] :
    ramificationIdx R S * finrank (ResidueField R) (ResidueField S) = finrank F E := by
  let : FaithfulSMul R S := inferInstance
  let : Module.Flat R S := inferInstance
  have h := ramificationIdx_mul_inertiaDeg_eq_finrank R S F E
  rw [Ideal.inertiaDeg_eq_of_isMaximal (p := maximalIdeal R)] at h
  exact h

private theorem pureComplete_coprime_indices
    {p m e f a g b h c i : ℕ} (hp : p.Prime) (hcop : p.Coprime m)
    (hRS : e * f = p) (hRT : a * g = m) (hTU : b * h = p) (hSU : c * i = m)
    (ht : e * c = a * b) : b = e ∧ c = a ∧ h = f := by
  have hnot : ¬p ∣ m := hp.coprime_iff_not_dvd.mp hcop
  have hediv : e ∣ p := ⟨f, hRS.symm⟩
  have hbdiv : b ∣ p := ⟨h, hTU.symm⟩
  have hadiv : a ∣ m := ⟨g, hRT.symm⟩
  have hcdiv : c ∣ m := ⟨i, hSU.symm⟩
  have hbe : b = e := by
    rcases (Nat.dvd_prime hp).mp hediv with he | he <;>
      rcases (Nat.dvd_prime hp).mp hbdiv with hb | hb
    · exact hb.trans he.symm
    · exfalso
      apply hnot
      apply dvd_trans _ hcdiv
      refine ⟨a, ?_⟩
      simpa only [he, hb, one_mul, Nat.mul_comm] using ht
    · exfalso
      apply hnot
      apply dvd_trans _ hadiv
      refine ⟨c, ?_⟩
      simpa only [he, hb, mul_one] using ht.symm
    · exact hb.trans he.symm
  have he0 : e ≠ 0 := by
    intro he
    rw [he, zero_mul] at hRS
    exact hp.ne_zero hRS.symm
  have hca : c = a := mul_left_cancel₀ he0 (by
    simpa only [hbe, Nat.mul_comm a e] using ht)
  have hhf : h = f := mul_left_cancel₀ he0 (by
    simpa only [hbe] using hTU.trans hRS.symm)
  exact ⟨hbe, hca, hhf⟩

private theorem pureComplete_residue_map_ramification
    (R S F E : Type u)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Algebra R S] [FaithfulSMul R S] [IsLocalHom (algebraMap R S)]
    [Field F] [Algebra R F] [IsFractionRing R F]
    [Field E] [Algebra S E] [IsFractionRing S E]
    [Algebra R E] [Algebra F E] [IsScalarTower R F E] [IsScalarTower R S E]
    (n : ℕ) (x : MilnorKTheory F (n + 1)) :
    dvrMilnorTameSymbol' S E n (milnorKTheoryMap (algebraMap F E) (n + 1) x) =
      (ramificationIdx R S : ℤ) •
        milnorKTheoryMap (algebraMap (ResidueField R) (ResidueField S)) n
          (dvrMilnorTameSymbol' R F n x) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨ρ, hρ⟩ := IsDiscreteValuationRing.exists_irreducible S
  obtain ⟨e, z, hz⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R S)).mpr hπ.ne_zero) hρ
  have he : e = ramificationIdx R S := by
    have h := addVal_algebraMap_eq_ramificationIdx R S π hπ
    rw [hz, IsDiscreteValuationRing.addVal_def' z hρ e] at h
    exact_mod_cast h
  have hf : ∀ r : R, algebraMap F E (algebraMap R F r) =
      algebraMap S E (algebraMap R S r) := fun r =>
    (IsScalarTower.algebraMap_apply R F E r).symm.trans
      (IsScalarTower.algebraMap_apply R S E r)
  have h := DFunLike.congr_fun
    (dvrMilnorTameSymbol'_map_ramified (algebraMap R S) (algebraMap F E) hf
      hπ hρ z e hz n) x
  have hκ : ResidueField.map (algebraMap R S) =
      algebraMap (ResidueField R) (ResidueField S) := rfl
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.smul_apply, he, hκ] at h
  exact h

section SuppliedSquare

variable (R S T U F E L M : Type u)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
  [CommRing U] [IsDomain U] [IsDiscreteValuationRing U]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
  [IsLocalHom (algebraMap R S)]
  [Algebra R T] [Module.Finite R T] [Module.IsTorsionFree R T]
  [IsLocalHom (algebraMap R T)]
  [Algebra S U] [Module.Finite S U] [Module.IsTorsionFree S U]
  [IsLocalHom (algebraMap S U)]
  [Algebra T U] [Module.Finite T U] [Module.IsTorsionFree T U]
  [IsLocalHom (algebraMap T U)]
  [Algebra R U] [IsScalarTower R S U] [IsScalarTower R T U]
  [Field F] [Algebra R F] [IsFractionRing R F]
  [Field E] [Algebra S E] [IsFractionRing S E] [Algebra F E]
  [Algebra R E] [IsScalarTower R F E] [IsScalarTower R S E]
  [Field L] [Algebra T L] [IsFractionRing T L] [Algebra F L]
  [Algebra R L] [IsScalarTower R F L] [IsScalarTower R T L]
  [Field M] [Algebra U M] [IsFractionRing U M]
  [Algebra F M] [Algebra E M] [Algebra L M]
  [IsScalarTower F E M] [IsScalarTower F L M]
  [Algebra S M] [IsScalarTower S E M] [IsScalarTower S U M]
  [Algebra T M] [IsScalarTower T L M] [IsScalarTower T U M]
  [FiniteDimensional F E] [FiniteDimensional F L]
  [FiniteDimensional L M] [FiniteDimensional E M]

/-- The actual coprime square preserves the vertical ramification and residue
degrees, and the horizontal ramification indices agree as well. -/
theorem ramification_and_residue_finrank_eq_of_coprime_prime_square
    (hp : Nat.Prime (finrank F E)) (hcop : (finrank F E).Coprime (finrank F L))
    (hdegree : finrank L M = finrank F E) :
    ramificationIdx T U = ramificationIdx R S ∧
      ramificationIdx S U = ramificationIdx R T ∧
      finrank (ResidueField T) (ResidueField U) =
        finrank (ResidueField R) (ResidueField S) := by
  let : FiniteDimensional F M := Module.Finite.trans L M
  have hEM : finrank E M = finrank F L := mul_left_cancel₀ hp.ne_zero (by
    have h := (finrank_mul_finrank F E M).trans (finrank_mul_finrank F L M).symm
    simpa only [hdegree, Nat.mul_comm (finrank F L) (finrank F E)] using h)
  have hRS := pureComplete_local_degree R S F E
  have hRT := pureComplete_local_degree R T F L
  have hTU := pureComplete_local_degree T U L M
  have hSU := pureComplete_local_degree S U E M
  rw [hdegree] at hTU
  rw [hEM] at hSU
  have ht : ramificationIdx R S * ramificationIdx S U =
      ramificationIdx R T * ramificationIdx T U := by
    have hS := (IsDiscreteValuationRing.ramificationIdx_and_inertiaDeg_tower R S U).1
    have hT := (IsDiscreteValuationRing.ramificationIdx_and_inertiaDeg_tower R T U).1
    simpa only [ramificationIdx_def,
      Ideal.ramificationIdx'_eq_ramificationIdx (maximalIdeal R) (maximalIdeal S)
        (IsDiscreteValuationRing.not_a_field R),
      Ideal.ramificationIdx'_eq_ramificationIdx (maximalIdeal S) (maximalIdeal U)
        (IsDiscreteValuationRing.not_a_field S),
      Ideal.ramificationIdx'_eq_ramificationIdx (maximalIdeal R) (maximalIdeal T)
        (IsDiscreteValuationRing.not_a_field R),
      Ideal.ramificationIdx'_eq_ramificationIdx (maximalIdeal T) (maximalIdeal U)
        (IsDiscreteValuationRing.not_a_field T)] using hS.symm.trans hT
  exact pureComplete_coprime_indices hp hcop hRS hRT hTU hSU ht

variable [IsPurelyInseparable F E] [IsPurelyInseparable L M]

/-- The actual residue norm square in the coprime pure-prime DVR diagram.
The residue degree-one case uses the native degree-one norm identity. -/
theorem milnorKNormRing_residue_baseChange_of_coprime_pure_prime_square
    (hp : Nat.Prime (finrank F E)) (hcop : (finrank F E).Coprime (finrank F L))
    (hdegree : finrank L M = finrank F E) (y : MilnorKRing (ResidueField S)) :
    milnorKRingMap (algebraMap (ResidueField R) (ResidueField T))
        (milnorKNormRing (ResidueField R) (ResidueField S) y) =
      milnorKNormRing (ResidueField T) (ResidueField U)
        (milnorKRingMap (algebraMap (ResidueField S) (ResidueField U)) y) := by
  let : IsLocalHom (algebraMap R U) := by
    rw [IsScalarTower.algebraMap_eq R S U]
    infer_instance
  let : IsPurelyInseparable (ResidueField R) (ResidueField S) :=
    dvr_residueField_isPurelyInseparable R S F E
  let : IsPurelyInseparable (ResidueField T) (ResidueField U) :=
    dvr_residueField_isPurelyInseparable T U L M
  have hres :=
    (ramification_and_residue_finrank_eq_of_coprime_prime_square
      R S T U F E L M hp hcop hdegree).2.2
  have hRS := pureComplete_local_degree R S F E
  have hRT := pureComplete_local_degree R T F L
  have hfdvd : finrank (ResidueField R) (ResidueField S) ∣ finrank F E :=
    ⟨ramificationIdx R S, by simpa only [Nat.mul_comm] using hRS.symm⟩
  rcases (Nat.dvd_prime hp).mp hfdvd with hf | hf
  · have hb := Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hf
    let z := milnorKNormRing (ResidueField R) (ResidueField S) y
    have hy : milnorKRingMap (algebraMap (ResidueField R) (ResidueField S)) z = y := by
      dsimp only [z]
      rw [milnorKNormRing_of_bijective hb]
      let g := RingEquiv.ofBijective (algebraMap (ResidueField R) (ResidueField S)) hb
      change milnorKRingMap g.toRingHom (milnorKRingMap g.symm.toRingHom y) = y
      have hg : g.toRingHom.comp g.symm.toRingHom = RingHom.id (ResidueField S) :=
        RingHom.ext fun z => g.apply_symm_apply z
      rw [milnorKRingMap_comp_apply, hg, milnorKRingMap_id_apply]
    have hn : milnorKNormRing (ResidueField T) (ResidueField U)
        (milnorKRingMap (algebraMap (ResidueField S) (ResidueField U)) y) =
        (finrank (ResidueField T) (ResidueField U) : ℤ) •
          milnorKRingMap (algebraMap (ResidueField R) (ResidueField T)) z := by
      rw [← hy, milnorKRingMap_comp_apply, ← IsScalarTower.algebraMap_eq,
        IsScalarTower.algebraMap_eq (ResidueField R) (ResidueField T) (ResidueField U),
        ← milnorKRingMap_comp_apply, milnorKNormRing_milnorKRingMap]
    simpa only [hres, hf, Nat.cast_one, one_smul] using hn.symm
  · have hgdvd : finrank (ResidueField R) (ResidueField T) ∣ finrank F L :=
      ⟨ramificationIdx R T, by simpa only [Nat.mul_comm] using hRT.symm⟩
    have hcop' : (finrank F E).Coprime (finrank (ResidueField R) (ResidueField T)) :=
      hp.coprime_iff_not_dvd.mpr (fun h =>
        (hp.coprime_iff_not_dvd.mp hcop) (dvd_trans h hgdvd))
    exact milnorKNormRing_baseChange_of_prime_of_isPurelyInseparable_of_coprime
      (hf.symm ▸ hp) (hf.symm ▸ hcop') hres y

include U in
/-- A mixed witness upstairs kills the restriction of the original error,
weighted by the actual auxiliary ramification index. -/
theorem ramification_smul_restrict_norm_residue_difference_eq_zero_of_coprime_pure_prime_square
    (hp : Nat.Prime (finrank F E)) (hcop : (finrank F E).Coprime (finrank F L))
    (hdegree : finrank L M = finrank F E) (n : ℕ) (x : MilnorKTheory E (n + 1))
    (hmixed : milnorKTheoryMap (algebraMap E M) (n + 1) x ∈
      milnorKMixedSpan (algebraMap L M) n) :
    (ramificationIdx R T : ℤ) •
      milnorKTheoryMap (algebraMap (ResidueField R) (ResidueField T)) n
        (dvrMilnorTameSymbol' R F n (milnorKNorm F E (n + 1) x) -
          milnorKNorm (ResidueField R) (ResidueField S) n
            (dvrMilnorTameSymbol' S E n x)) = 0 := by
  have hindices := ramification_and_residue_finrank_eq_of_coprime_prime_square
    R S T U F E L M hp hcop hdegree
  have hupper := milnorKNorm_baseChange_of_prime_of_isPurelyInseparable_of_coprime
    hp hcop hdegree (n + 1) x
  have hR := pureComplete_residue_map_ramification R T F L n
    (milnorKNorm F E (n + 1) x)
  have hS := pureComplete_residue_map_ramification S U E M n x
  have hbranch := dvrMilnorTameSymbol'_milnorKNorm_of_mem_mixedSpan_of_isPurelyInseparable_of_prime
    T U L M (hdegree.symm ▸ hp) n _ hmixed
  have hlower :
      milnorKTheoryMap (algebraMap (ResidueField R) (ResidueField T)) n
          (milnorKNorm (ResidueField R) (ResidueField S) n
            (dvrMilnorTameSymbol' S E n x)) =
        milnorKNorm (ResidueField T) (ResidueField U) n
          (milnorKTheoryMap (algebraMap (ResidueField S) (ResidueField U)) n
            (dvrMilnorTameSymbol' S E n x)) := by
    simp only [milnorKTheoryMap_eq_transport]
    apply Subtype.ext
    exact milnorKNormRing_residue_baseChange_of_coprime_pure_prime_square
      R S T U F E L M hp hcop hdegree (dvrMilnorTameSymbol' S E n x : MilnorKRing _)
  rw [map_sub, smul_sub]
  apply sub_eq_zero.mpr
  calc
    _ = dvrMilnorTameSymbol' T L n
        (milnorKTheoryMap (algebraMap F L) (n + 1) (milnorKNorm F E (n + 1) x)) := hR.symm
    _ = dvrMilnorTameSymbol' T L n
        (milnorKNorm L M (n + 1) (milnorKTheoryMap (algebraMap E M) (n + 1) x)) :=
      congrArg (dvrMilnorTameSymbol' T L n) hupper
    _ = milnorKNorm (ResidueField T) (ResidueField U) n
        (dvrMilnorTameSymbol' U M n
          (milnorKTheoryMap (algebraMap E M) (n + 1) x)) := hbranch
    _ = _ := by rw [hS, map_zsmul, hindices.2.1, ← hlower]

include T U in
/-- A genuine mixed witness in the supplied coprime DVR square proves the
original all-symbol equality for this class, by two explicit annihilators. -/
theorem dvrMilnorTameSymbol'_milnorKNorm_of_coprime_pure_prime_square
    (hp : Nat.Prime (finrank F E)) (hcop : (finrank F E).Coprime (finrank F L))
    (hdegree : finrank L M = finrank F E) (n : ℕ) (x : MilnorKTheory E (n + 1))
    (hmixed : milnorKTheoryMap (algebraMap E M) (n + 1) x ∈
      milnorKMixedSpan (algebraMap L M) n) :
    dvrMilnorTameSymbol' R F n (milnorKNorm F E (n + 1) x) =
      milnorKNorm (ResidueField R) (ResidueField S) n (dvrMilnorTameSymbol' S E n x) := by
  let δ : MilnorKTheory (ResidueField R) n :=
    dvrMilnorTameSymbol' R F n (milnorKNorm F E (n + 1) x) -
      milnorKNorm (ResidueField R) (ResidueField S) n (dvrMilnorTameSymbol' S E n x)
  have hw := ramification_smul_restrict_norm_residue_difference_eq_zero_of_coprime_pure_prime_square
    R S T U F E L M hp hcop hdegree n x hmixed
  change (ramificationIdx R T : ℤ) •
    milnorKTheoryMap (algebraMap (ResidueField R) (ResidueField T)) n δ = 0 at hw
  have hr : (ramificationIdx R T : ℤ) •
      milnorKRingMap (algebraMap (ResidueField R) (ResidueField T))
        (δ : MilnorKRing (ResidueField R)) = 0 := by
    have h := congrArg ((milnorKGrading (ResidueField T) n).subtype) hw
    simpa only [map_zsmul, map_zero, milnorKTheoryMap_eq_transport,
      AddMonoidHom.coe_toIntLinearMap, AddSubgroup.subtype_apply, milnorKTransport_coe] using h
  have hn := congrArg (milnorKNormRing (ResidueField R) (ResidueField T)) hr
  rw [map_zsmul, milnorKNormRing_milnorKRingMap, map_zero, smul_smul,
    ← Nat.cast_mul, pureComplete_local_degree R T F L] at hn
  have haux : (finrank F L : ℤ) • δ = 0 := Subtype.ext hn
  have hprime : (finrank F E : ℤ) • δ = 0 :=
    finrank_smul_norm_residue_difference_eq_zero_of_isPurelyInseparable R S F E n x
  apply sub_eq_zero.mp
  have h := intGCD_nsmul_eq_zero.mpr ⟨hprime, haux⟩
  simpa only [Int.gcd_natCast_natCast, hcop.gcd_eq_one, one_nsmul] using h

end SuppliedSquare

end Stacks.Chow

end
