/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.DVRPrimeCharZero
public import Colib.RingTheory.KTheory.MilnorK.Norm.DVRExtensionDegreeOne
public import Colib.RingTheory.KTheory.MilnorK.Norm.DVRSquareTower
public import Colib.RingTheory.DiscreteValuationRing.CompleteExtension
public import Colib.RingTheory.IntegralClosure.IntermediateTower
public import Colib.FieldTheory.PGroupNormalSubfieldEmbedding

/-!
# Complete-DVR norm-residue compatibility in a p-group ambient

Actual normal-prime intermediate fields give strict degree descent. All
intermediate integral-closure maps are literal, and the original upper DVR is
retained. No unramifiedness or residue compatibility premise is assumed.

Adapted from `Aglib/KTheory/MilnorK/Norm/FiniteExtension/CompletePGroup.lean`
at revision `4f65be4eafa8964bd1f7a83682e99aa8165bd418`. The original strong
induction and actual intermediate closure are retained. Its prime step is the
already migrated native prime-Galois norm-residue theorem, which does not need
completeness. All conclusions concern the native chosen norm.
-/

@[expose] public noncomputable section

namespace Stacks.Chow

open IsLocalRing IsDiscreteValuationRing.CompleteExtension

universe u

/-- Complete-DVR compatibility for every extension embedded in a Galois p-group. -/
theorem dvrMilnorTameSymbol'_milnorKNorm_complete_of_pGroup
    (R S F E Ω : Type u)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (maximalIdeal R) R] [CharZero (ResidueField R)]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field F] [CharZero F] [Field E] [CharZero E] [Field Ω]
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
    · exact dvrMilnorTameSymbol'_milnorKNorm_of_finrank_eq_one R S F E hdeg n x
    have hgt : 1 < Module.finrank F E := by
      have := Module.finrank_pos (R := F) (M := E)
      omega
    obtain ⟨J, hnormal, hdegree, hdrop⟩ :=
      IntermediateField.exists_normal_prime_subfield_of_embedding ℓ hG g hgt
    let : Normal F J := hnormal
    let : CharZero J := charZero_of_injective_algebraMap (algebraMap F J).injective
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
    let : IsDiscreteValuationRing T := integralClosure_isDiscreteValuationRing R F J
    let : IsLocalHom (algebraMap R T) := integralClosure_isLocalHom R F J
    let : Module.Finite R T := IsIntegralClosure.finite R F J T
    let : IsFractionRing T J := IsIntegralClosure.isFractionRing_of_finite_extension R F J T
    let : IsAdicComplete (maximalIdeal T) T := integralClosure_isAdicComplete R F J
    let : Module.Finite (ResidueField R) (ResidueField T) :=
      integralClosure_residue_finite R F J
    let : CharZero (ResidueField T) :=
      charZero_of_injective_algebraMap (algebraMap (ResidueField R) (ResidueField T)).injective
    let : Algebra T S := IsIntegralClosure.IntermediateTower.closureAlgebra R S J E
    let : IsScalarTower R T S := IsIntegralClosure.IntermediateTower.baseTower R S J E
    let : IsScalarTower T S E := IsIntegralClosure.IntermediateTower.topTower R S J E
    let : IsIntegralClosure S T E :=
      IsIntegralClosure.IntermediateTower.upper_isIntegralClosure R S J E
    let : Module.Finite T S := IsIntegralClosure.IntermediateTower.upper_finite R S J E
    let : IsLocalHom (algebraMap T S) :=
      IsIntegralClosure.IntermediateTower.upper_isLocalHom R S J E
    have hprime : (Module.finrank F J).Prime := hdegree ▸ (Fact.out : ℓ.Prime)
    apply dvrMilnorTameSymbol'_milnorKNorm_of_tower R T S F J E n
    · let : IsGalois F J := ⟨⟩
      let : Module.IsTorsionFree R T := Module.isTorsionFree_iff_algebraMap_injective.mpr
        (integralClosure_algebraMap_injective R F J)
      exact dvrMilnorTameSymbol'_milnorKNorm_of_prime_galois_of_charZero R T F J hprime n
    · intro y
      apply ih (Module.finrank J E) (hd ▸ hdrop) T S J E Ω
      · exact hJG
      · exact IsScalarTower.toAlgHom J E Ω
      · rfl

end Stacks.Chow


end
