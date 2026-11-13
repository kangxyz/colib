/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.DVRCompletePrime
public import Colib.RingTheory.KTheory.MilnorK.Norm.DVRPurePrimeComplete
public import Colib.RingTheory.KTheory.MilnorK.Norm.DVRSquareFinite
public import Colib.RingTheory.DiscreteValuationRing.CompleteExtensionFinite
public import Colib.RingTheory.IntegralClosure.IntermediateTower
public import Colib.FieldTheory.PGroupNormalSubfieldEmbedding
public import Colib.FieldTheory.PurelyInseparable.NormalPrimePower

/-!
# Complete DVR norms in prime-power towers

The prime-Galois and prime purely inseparable norm-residue squares compose
along the actual towers of subfields and integral closures.
-/

@[expose] public noncomputable section

namespace Stacks.Chow

open IsLocalRing IsDiscreteValuationRing.CompleteExtension

universe u

/-- Complete-DVR compatibility for an extension embedded in a Galois p-group. -/
theorem dvrMilnorTameSymbol'_milnorKNorm_complete_of_pGroup_finite
    (R S F E Ω : Type u)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (maximalIdeal R) R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field F] [Field E] [Field Ω]
    [Algebra R F] [IsFractionRing R F]
    [Algebra F E] [FiniteDimensional F E] [Algebra R E] [IsScalarTower R F E]
    [Algebra R S] [Module.Finite R S] [IsLocalHom (algebraMap R S)]
    [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
    [IsIntegralClosure S R E]
    [Algebra F Ω] [FiniteDimensional F Ω] [IsGalois F Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] (hG : IsPGroup ℓ (Ω ≃ₐ[F] Ω)) (g : E →ₐ[F] Ω)
    (n : ℕ) (x : MilnorKTheory E (n + 1)) :
    dvrMilnorTameSymbol' R F n (milnorKNorm F E (n + 1) x) =
      milnorKNorm (ResidueField R) (ResidueField S) n (dvrMilnorTameSymbol' S E n x) := by
  induction hd : Module.finrank F E using Nat.strong_induction_on
      generalizing R S F E Ω with
  | h d ih =>
    by_cases hdeg : Module.finrank F E = 1
    · exact dvrMilnorTameSymbol'_milnorKNorm_of_finrank_eq_one_of_finite R S F E hdeg n x
    have hgt : 1 < Module.finrank F E := by
      have := Module.finrank_pos (R := F) (M := E)
      omega
    obtain ⟨J, hnormal, hdegree, hdrop⟩ :=
      IntermediateField.exists_normal_prime_subfield_of_embedding ℓ hG g hgt
    let : Normal F J := hnormal
    let : Algebra.IsSeparable F J := Algebra.IsSeparable.of_algHom F Ω (g.comp J.val)
    let : Algebra E Ω := g.toRingHom.toAlgebra
    let : IsScalarTower F E Ω := IsScalarTower.of_algebraMap_eq' g.comp_algebraMap.symm
    let : FiniteDimensional J E := FiniteDimensional.right F J E
    let : FiniteDimensional J Ω := FiniteDimensional.right F J Ω
    let : IsGalois J Ω := IsGalois.tower_top_of_isGalois F J Ω
    have hJG : IsPGroup ℓ (Ω ≃ₐ[J] Ω) :=
      hG.of_injective (AlgEquiv.restrictScalarsHom F)
        (AlgEquiv.restrictScalarsHom_injective F)
    let : IsScalarTower R J E := IsScalarTower.of_algebraMap_eq fun r => by
      rw [IsScalarTower.algebraMap_apply R F E, IsScalarTower.algebraMap_apply R F J,
        IsScalarTower.algebraMap_apply F J E]
    let T := integralClosure R J
    let : IsDiscreteValuationRing T := integralClosure_isDiscreteValuationRing_of_finite R F J
    let : IsLocalHom (algebraMap R T) := integralClosure_isLocalHom R F J
    let : Module.Finite R T := integralClosure_finite_of_finite R F J
    let : IsFractionRing T J := IsIntegralClosure.isFractionRing_of_finite_extension R F J T
    let : IsAdicComplete (maximalIdeal T) T := integralClosure_isAdicComplete_of_finite R F J
    let : Module.Finite (ResidueField R) (ResidueField T) :=
      integralClosure_residue_finite_of_finite R F J
    let : Algebra T S := IsIntegralClosure.IntermediateTower.closureAlgebra R S J E
    let : IsScalarTower R T S := IsIntegralClosure.IntermediateTower.baseTower R S J E
    let : IsScalarTower T S E := IsIntegralClosure.IntermediateTower.topTower R S J E
    let : IsIntegralClosure S T E :=
      IsIntegralClosure.IntermediateTower.upper_isIntegralClosure R S J E
    let : Module.Finite T S := IsIntegralClosure.IntermediateTower.upper_finite R S J E
    let : IsLocalHom (algebraMap T S) :=
      IsIntegralClosure.IntermediateTower.upper_isLocalHom R S J E
    have hprime : (Module.finrank F J).Prime := hdegree ▸ (Fact.out : ℓ.Prime)
    apply dvrMilnorTameSymbol'_milnorKNorm_of_tower_of_finite R T S F J E n
    · let : IsGalois F J := ⟨⟩
      let : Module.IsTorsionFree R T := Module.isTorsionFree_iff_algebraMap_injective.mpr
        (integralClosure_algebraMap_injective R F J)
      exact dvrMilnorTameSymbol'_milnorKNorm_complete_of_prime_galois R T F J hprime n
    · intro y
      apply ih (Module.finrank J E) (hd ▸ hdrop) T S J E Ω
      · exact hJG
      · exact IsScalarTower.toAlgHom J E Ω
      · rfl

/-- Complete-DVR compatibility for every finite purely inseparable extension. -/
theorem dvrMilnorTameSymbol'_milnorKNorm_complete_of_isPurelyInseparable_finite
    (R S F E : Type u)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (maximalIdeal R) R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field F] [Field E]
    [Algebra R F] [IsFractionRing R F]
    [Algebra F E] [FiniteDimensional F E] [Algebra R E] [IsScalarTower R F E]
    [Algebra R S] [Module.Finite R S] [IsLocalHom (algebraMap R S)]
    [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
    [IsIntegralClosure S R E] [IsPurelyInseparable F E]
    (n : ℕ) (x : MilnorKTheory E (n + 1)) :
    dvrMilnorTameSymbol' R F n (milnorKNorm F E (n + 1) x) =
      milnorKNorm (ResidueField R) (ResidueField S) n (dvrMilnorTameSymbol' S E n x) := by
  induction hd : Module.finrank F E using Nat.strong_induction_on generalizing R S F E with
  | h d ih =>
    by_cases hone : Module.finrank F E = 1
    · exact dvrMilnorTameSymbol'_milnorKNorm_of_finrank_eq_one_of_finite R S F E hone n x
    obtain ⟨p, _⟩ := ExpChar.exists F
    obtain ⟨r, hr⟩ := IsPurelyInseparable.finrank_eq_pow F E p
    have hp : p.Prime := (expChar_is_prime_or_one F p).resolve_right fun he =>
      hone (hr.trans (by rw [he, one_pow]))
    let : Fact p.Prime := ⟨hp⟩
    let : CharP F p := (expChar_prime_iff F hp).mp inferInstance
    have hgt : 1 < Module.finrank F E :=
      lt_of_le_of_ne (Nat.succ_le_of_lt Module.finrank_pos) (Ne.symm hone)
    obtain ⟨J, _, hJ⟩ := IntermediateField.exists_normal_prime_subfield_of_finrank_pow_embedding
      p r hr (AlgHom.id F E) hgt
    let : IsPurelyInseparable F J := IsPurelyInseparable.tower_bot F J E
    let : IsPurelyInseparable J E := IsPurelyInseparable.tower_top F J E
    let : FiniteDimensional J E := FiniteDimensional.right F J E
    have hdrop : Module.finrank J E < d := by
      rw [← hd, ← Module.finrank_mul_finrank F J E, hJ]
      exact lt_mul_of_one_lt_left Module.finrank_pos hp.one_lt
    let : IsScalarTower R J E := IsScalarTower.of_algebraMap_eq fun a => by
      rw [IsScalarTower.algebraMap_apply R F E, IsScalarTower.algebraMap_apply R F J,
        IsScalarTower.algebraMap_apply F J E]
    let T := integralClosure R J
    let : IsDiscreteValuationRing T := integralClosure_isDiscreteValuationRing_of_finite R F J
    let : IsLocalHom (algebraMap R T) := integralClosure_isLocalHom R F J
    let : Module.Finite R T := integralClosure_finite_of_finite R F J
    let : IsFractionRing T J := IsIntegralClosure.isFractionRing_of_finite_extension R F J T
    let : IsAdicComplete (maximalIdeal T) T := integralClosure_isAdicComplete_of_finite R F J
    let : Module.Finite (ResidueField R) (ResidueField T) :=
      integralClosure_residue_finite_of_finite R F J
    let : Algebra T S := IsIntegralClosure.IntermediateTower.closureAlgebra R S J E
    let : IsScalarTower R T S := IsIntegralClosure.IntermediateTower.baseTower R S J E
    let : IsScalarTower T S E := IsIntegralClosure.IntermediateTower.topTower R S J E
    let : IsIntegralClosure S T E :=
      IsIntegralClosure.IntermediateTower.upper_isIntegralClosure R S J E
    let : Module.Finite T S := IsIntegralClosure.IntermediateTower.upper_finite R S J E
    let : IsLocalHom (algebraMap T S) :=
      IsIntegralClosure.IntermediateTower.upper_isLocalHom R S J E
    apply dvrMilnorTameSymbol'_milnorKNorm_of_tower_of_finite R T S F J E n
    · let : Module.IsTorsionFree R T := Module.isTorsionFree_iff_algebraMap_injective.mpr
        (integralClosure_algebraMap_injective R F J)
      exact dvrMilnorTameSymbol'_milnorKNorm_of_complete_of_isPurelyInseparable_of_prime
        R T F J (hJ.symm ▸ hp) n
    · intro y
      exact ih (Module.finrank J E) hdrop T S J E y rfl

end Stacks.Chow

end
