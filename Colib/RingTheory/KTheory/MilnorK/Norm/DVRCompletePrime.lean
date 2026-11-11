/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.DiscreteValuationRing.CompleteExtensionFinite
public import Colib.RingTheory.IntegralClosure.IntermediateTower
public import Colib.RingTheory.KTheory.MilnorK.FiniteMixedGenerationArbitrary
public import Colib.RingTheory.KTheory.MilnorK.Norm.DVRMixedPrime
public import Colib.RingTheory.KTheory.MilnorK.Norm.DVRPrimeAnnihilation
public import Colib.RingTheory.KTheory.MilnorK.Norm.DVRPurePrimeCoprimeDescent
public import Colib.RingTheory.KTheory.MilnorK.Norm.DVRRestrictionKernel
public import Colib.RingTheory.KTheory.MilnorK.Norm.PrimeCoprimeBaseChangeFinite

/-!
# The norm and tame residue in complete prime Galois extensions

The original prime degree kills the norm-residue discrepancy. A finite
coefficient extension of coprime degree gives a mixed expansion and a square
of actual finite complete DVR extensions. Both vertical residue degrees and
both horizontal ramification indices agree in this square. The residue norm
of the ramification-weighted restriction yields the second annihilator.
-/

@[expose] public noncomputable section

open IsLocalRing Module Polynomial IntermediateField
open IsDiscreteValuationRing.CompleteExtension
open Stacks.DiscreteValuationRing.Ramification

universe u

namespace Stacks.Chow

private theorem completePrime_residue_degree_dvd
    (R S F E : Type u)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
    [IsLocalHom (algebraMap R S)]
    [Field F] [Algebra R F] [IsFractionRing R F]
    [Field E] [Algebra F E] [Algebra R E] [IsScalarTower R F E]
    [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E] :
    finrank (ResidueField R) (ResidueField S) ∣ finrank F E := by
  let : FaithfulSMul R S := inferInstance
  let : Module.Flat R S := inferInstance
  have h := ramificationIdx_mul_inertiaDeg_eq_finrank R S F E
  rw [Ideal.inertiaDeg_eq_of_isMaximal (p := maximalIdeal R)] at h
  have hdegree : ramificationIdx R S * finrank (ResidueField R) (ResidueField S) =
      finrank F E := h
  exact ⟨ramificationIdx R S, hdegree.symm.trans (Nat.mul_comm _ _)⟩

private theorem completePrime_ramificationIdx
    {R S : Type u}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Algebra R S] [FaithfulSMul R S] {π : R} {ρ : S}
    (hπ : Irreducible π) (hρ : Irreducible ρ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ρ ^ e) :
    e = ramificationIdx R S := by
  have h := addVal_algebraMap_eq_ramificationIdx R S π hπ
  rw [he, IsDiscreteValuationRing.addVal_def' u hρ e] at h
  exact_mod_cast h

private theorem completePrime_map_residue
    (R S F E : Type u)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    [Field F] [Algebra R F] [IsFractionRing R F]
    [Field E] [Algebra F E] [Algebra R E] [IsScalarTower R F E]
    [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
    {π : R} {ρ : S} (hπ : Irreducible π) (hρ : Irreducible ρ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ρ ^ e)
    (n : ℕ) (x : MilnorKTheory F (n + 1)) :
    dvrMilnorTameSymbol' S E n (milnorKTheoryMap (algebraMap F E) (n + 1) x) =
      e • milnorKTheoryMap (algebraMap (ResidueField R) (ResidueField S)) n
        (dvrMilnorTameSymbol' R F n x) := by
  have hf (r : R) : algebraMap F E (algebraMap R F r) =
      algebraMap S E (algebraMap R S r) :=
    (IsScalarTower.algebraMap_apply R F E r).symm.trans
      (IsScalarTower.algebraMap_apply R S E r)
  have h := DFunLike.congr_fun
    (dvrMilnorTameSymbol'_map_ramified (algebraMap R S) (algebraMap F E) hf
      hπ hρ u e he n) x
  have hκ : ResidueField.map (algebraMap R S) =
      algebraMap (ResidueField R) (ResidueField S) := rfl
  simpa only [AddMonoidHom.comp_apply, AddMonoidHom.smul_apply, LinearMap.toAddMonoidHom_coe,
    natCast_zsmul, hκ] using h

section CoprimeSquare

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

private theorem completePrime_residue_norm_baseChange
    (hp : Nat.Prime (finrank F E)) (hcop : (finrank F E).Coprime (finrank F L))
    (hdegree : finrank L M = finrank F E) (y : MilnorKRing (ResidueField S)) :
    milnorKRingMap (algebraMap (ResidueField R) (ResidueField T))
        (milnorKNormRing (ResidueField R) (ResidueField S) y) =
      milnorKNormRing (ResidueField T) (ResidueField U)
        (milnorKRingMap (algebraMap (ResidueField S) (ResidueField U)) y) := by
  let : IsLocalHom (algebraMap R U) := by
    rw [IsScalarTower.algebraMap_eq R S U]
    infer_instance
  have hres := (ramification_and_residue_finrank_eq_of_coprime_prime_square
    R S T U F E L M hp hcop hdegree).2.2
  have hfdvd := completePrime_residue_degree_dvd R S F E
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
  · have hgdvd := completePrime_residue_degree_dvd R T F L
    have hcop' : (finrank F E).Coprime (finrank (ResidueField R) (ResidueField T)) :=
      hp.coprime_iff_not_dvd.mpr (fun h =>
        (hp.coprime_iff_not_dvd.mp hcop) (dvd_trans h hgdvd))
    exact milnorKNormRing_baseChange_of_prime_of_coprime
      (hf.symm ▸ hp) (hf.symm ▸ hcop') hres y

variable [IsGalois F E]

include T U in
private theorem completePrime_of_coprime_mixed_square
    (hp : Nat.Prime (finrank F E)) (hcop : (finrank F E).Coprime (finrank F L))
    (hdegree : finrank L M = finrank F E) (n : ℕ) (x : MilnorKTheory E (n + 1))
    (hmixed : milnorKTheoryMap (algebraMap E M) (n + 1) x ∈
      milnorKMixedSpan (algebraMap L M) n) :
    dvrMilnorTameSymbol' R F n (milnorKNorm F E (n + 1) x) =
      milnorKNorm (ResidueField R) (ResidueField S) n (dvrMilnorTameSymbol' S E n x) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨τ, hτ⟩ := IsDiscreteValuationRing.exists_irreducible T
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S
  obtain ⟨ρ, hρ⟩ := IsDiscreteValuationRing.exists_irreducible U
  obtain ⟨a, _, v, ha⟩ := exists_positive_ramification
    (algebraMap R T) (FaithfulSMul.algebraMap_injective R T) hπ hτ
  obtain ⟨c, _, w, hc⟩ := exists_positive_ramification
    (algebraMap S U) (FaithfulSMul.algebraMap_injective S U) hϖ hρ
  obtain ⟨b, _, u, hb⟩ := exists_positive_ramification
    (algebraMap T U) (FaithfulSMul.algebraMap_injective T U) hτ hρ
  have hindices := ramification_and_residue_finrank_eq_of_coprime_prime_square
    R S T U F E L M hp hcop hdegree
  have hca : c = a := (completePrime_ramificationIdx hϖ hρ w c hc).trans
    (hindices.2.1.trans (completePrime_ramificationIdx hπ hτ v a ha).symm)
  have hupper :
      milnorKTheoryMap (algebraMap F L) (n + 1) (milnorKNorm F E (n + 1) x) =
        milnorKNorm L M (n + 1) (milnorKTheoryMap (algebraMap E M) (n + 1) x) := by
    simp only [milnorKTheoryMap_eq_transport]
    apply Subtype.ext
    exact milnorKNormRing_baseChange_of_prime_of_coprime hp hcop hdegree (x : MilnorKRing E)
  let y := dvrMilnorTameSymbol' S E n x
  have hlower :
      milnorKTheoryMap (algebraMap (ResidueField R) (ResidueField T)) n
          (milnorKNorm (ResidueField R) (ResidueField S) n y) =
        milnorKNorm (ResidueField T) (ResidueField U) n
          (milnorKTheoryMap (algebraMap (ResidueField S) (ResidueField U)) n y) := by
    simp only [milnorKTheoryMap_eq_transport]
    apply Subtype.ext
    exact completePrime_residue_norm_baseChange R S T U F E L M hp hcop hdegree
      (y : MilnorKRing (ResidueField S))
  have hR := completePrime_map_residue R T F L hπ hτ v a ha n
    (milnorKNorm F E (n + 1) x)
  have hS := completePrime_map_residue S U E M hϖ hρ w c hc n x
  have hbranch := dvrMilnorTameSymbol'_milnorKNorm_of_mem_mixedSpan_of_prime_degree_any
    T U L M hτ hρ u b hb (hdegree.symm ▸ hp) n _ hmixed
  let δ : MilnorKTheory (ResidueField R) n :=
    dvrMilnorTameSymbol' R F n (milnorKNorm F E (n + 1) x) -
      milnorKNorm (ResidueField R) (ResidueField S) n y
  have hrestrict :
      a • milnorKTheoryMap (algebraMap (ResidueField R) (ResidueField T)) n δ = 0 := by
    dsimp only [δ]
    rw [map_sub, smul_sub]
    apply sub_eq_zero.mpr
    calc
      _ = dvrMilnorTameSymbol' T L n
          (milnorKTheoryMap (algebraMap F L) (n + 1) (milnorKNorm F E (n + 1) x)) := hR.symm
      _ = dvrMilnorTameSymbol' T L n
          (milnorKNorm L M (n + 1) (milnorKTheoryMap (algebraMap E M) (n + 1) x)) :=
        congrArg (dvrMilnorTameSymbol' T L n) hupper
      _ = milnorKNorm (ResidueField T) (ResidueField U) n
          (dvrMilnorTameSymbol' U M n (milnorKTheoryMap (algebraMap E M) (n + 1) x)) := hbranch
      _ = _ := by rw [hS, map_nsmul, hca, ← hlower]
  have haux :=
    finrank_smul_eq_zero_of_ramified_residue_restrict R T F L hπ hτ v a ha n δ hrestrict
  have haux' : (finrank F L : ℤ) • δ = 0 := by simpa only [natCast_zsmul] using haux
  have hprime : (finrank F E : ℤ) • δ = 0 :=
    finrank_smul_norm_residue_difference_eq_zero R S F E hp n x
  apply sub_eq_zero.mp
  have h := intGCD_nsmul_eq_zero.mpr ⟨hprime, haux'⟩
  simpa only [Int.gcd_natCast_natCast, hcop.gcd_eq_one, one_nsmul] using h

end CoprimeSquare

private theorem completePrime_of_coprime_mixed_field
    (R S F E L M : Type u)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (maximalIdeal R) R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
    [IsLocalHom (algebraMap R S)]
    [Field F] [Algebra R F] [IsFractionRing R F]
    [Field E] [Algebra F E] [Algebra R E] [IsScalarTower R F E]
    [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
    [Field L] [Algebra F L]
    [Field M] [Algebra F M] [Algebra E M] [Algebra L M]
    [IsScalarTower F E M] [IsScalarTower F L M]
    [FiniteDimensional F E] [FiniteDimensional F L] [FiniteDimensional L M]
    [IsGalois F E]
    (hp : Nat.Prime (finrank F E)) (hcop : (finrank F E).Coprime (finrank F L))
    (hdegree : finrank L M = finrank F E) (n : ℕ) (x : MilnorKTheory E (n + 1))
    (hmixed : milnorKTheoryMap (algebraMap E M) (n + 1) x ∈
      milnorKMixedSpan (algebraMap L M) n) :
    dvrMilnorTameSymbol' R F n (milnorKNorm F E (n + 1) x) =
      milnorKNorm (ResidueField R) (ResidueField S) n (dvrMilnorTameSymbol' S E n x) := by
  let : FiniteDimensional F M := Module.Finite.trans L M
  let : FiniteDimensional E M := Module.Finite.of_restrictScalars_finite F E M
  let : Algebra R L := ((algebraMap F L).comp (algebraMap R F)).toAlgebra
  let : IsScalarTower R F L := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra R M := ((algebraMap L M).comp (algebraMap R L)).toAlgebra
  let : IsScalarTower R L M := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower R F M := IsScalarTower.of_algebraMap_eq fun r =>
    (IsScalarTower.algebraMap_apply F L M (algebraMap R F r)).symm
  let : Algebra S M := ((algebraMap E M).comp (algebraMap S E)).toAlgebra
  let : IsScalarTower S E M := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower R S M := IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap R M r = algebraMap E M (algebraMap S E (algebraMap R S r))
    rw [← IsScalarTower.algebraMap_apply R S E, IsScalarTower.algebraMap_apply R F E,
      ← IsScalarTower.algebraMap_apply F E M, ← IsScalarTower.algebraMap_apply R F M]
  let T := integralClosure R L
  let U := integralClosure R M
  let : IsDiscreteValuationRing T := integralClosure_isDiscreteValuationRing_of_finite R F L
  let : IsDiscreteValuationRing U := integralClosure_isDiscreteValuationRing_of_finite R F M
  let : IsLocalHom (algebraMap R T) := integralClosure_isLocalHom R F L
  let : Module.Finite R T := integralClosure_finite_of_finite R F L
  let : Module.Finite R U := integralClosure_finite_of_finite R F M
  let : IsFractionRing T L := IsIntegralClosure.isFractionRing_of_finite_extension R F L T
  let : IsFractionRing U M := IsIntegralClosure.isFractionRing_of_finite_extension R F M U
  let : Module.IsTorsionFree R T := Module.isTorsionFree_iff_algebraMap_injective.mpr
    (integralClosure_algebraMap_injective R F L)
  let j : S →ₐ[R] U := IsIntegralClosure.lift R U M
  let : Algebra S U := j.toRingHom.toAlgebra
  let : IsScalarTower R S U := IsScalarTower.of_algebraMap_eq fun r => (j.commutes r).symm
  let : IsScalarTower S U M := IsScalarTower.of_algebraMap_eq fun s =>
    (IsIntegralClosure.algebraMap_lift R U M s).symm
  let : Module.Finite S U := Module.Finite.of_restrictScalars_finite R S U
  have hinj : Function.Injective (algebraMap S U) := by
    intro s t h
    apply IsFractionRing.injective S E
    apply (algebraMap E M).injective
    change algebraMap S M s = algebraMap S M t
    rw [IsScalarTower.algebraMap_apply S U M, IsScalarTower.algebraMap_apply S U M, h]
  let : Module.IsTorsionFree S U := Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  let : IsLocalHom (algebraMap S U) :=
    (algebraMap_isIntegral_iff.mpr (inferInstance : Algebra.IsIntegral S U)).isLocalHom hinj
  let : Algebra T U := IsIntegralClosure.IntermediateTower.closureAlgebra R U L M
  let : IsScalarTower R T U := IsIntegralClosure.IntermediateTower.baseTower R U L M
  let : IsScalarTower T U M := IsIntegralClosure.IntermediateTower.topTower R U L M
  let : Module.Finite T U := IsIntegralClosure.IntermediateTower.upper_finite R U L M
  let : IsLocalHom (algebraMap T U) := IsIntegralClosure.IntermediateTower.upper_isLocalHom R U L M
  let : Module.IsTorsionFree T U := by
    apply Module.isTorsionFree_iff_algebraMap_injective.mpr
    intro a b h
    apply IsFractionRing.injective T L
    apply (algebraMap L M).injective
    change algebraMap T M a = algebraMap T M b
    rw [IsScalarTower.algebraMap_apply T U M, IsScalarTower.algebraMap_apply T U M, h]
  exact completePrime_of_coprime_mixed_square R S T U F E L M hp hcop hdegree n x hmixed

section Complete

attribute [local instance] Ideal.Quotient.field

variable (R S F E : Type u)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsAdicComplete (maximalIdeal R) R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
  [IsLocalHom (algebraMap R S)]
  [Field F] [Algebra R F] [IsFractionRing R F]
  [Field E] [Algebra F E] [Algebra R E] [IsScalarTower R F E]
  [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
  [FiniteDimensional F E] [IsGalois F E]

/-- The chosen norm commutes with the tame symbol for a finite local DVR
extension over a complete DVR of prime Galois fraction degree. -/
theorem dvrMilnorTameSymbol'_milnorKNorm_complete_of_prime_galois
    (hp : Nat.Prime (finrank F E)) (n : ℕ) (x : MilnorKTheory E (n + 1)) :
    dvrMilnorTameSymbol' R F n (milnorKNorm F E (n + 1) x) =
      milnorKNorm (ResidueField R) (ResidueField S) n (dvrMilnorTameSymbol' S E n x) := by
  classical
  refine (exists_selected_simpleMilnorNorm_presentation_of_prime hp).elim ?_
  intro a ha
  refine ha.elim ?_
  intro _ha he
  refine he.elim ?_
  intro e he
  have hdegree := he.1
  let p : F[X] := minpoly F a
  have hpmonic : p.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral (R := F) a)
  let : Fact (Irreducible p) :=
    ⟨minpoly.irreducible (Algebra.IsIntegral.isIntegral (R := F) a)⟩
  let g : E ≃ₐ[F] AdjoinRoot p := { toRingEquiv := e.toRingEquiv, commutes' := e.commutes }
  let y : MilnorKTheory (AdjoinRoot p) (n + 1) := milnorKTheoryMap g.toRingHom (n + 1) x
  refine (exists_finite_coprime_milnorK_mixed_expansion_arbitrary p hpmonic
    (hdegree.symm ▸ hp) n y).elim ?_
  intro s hs
  refine hs.2.elim ?_
  intro L hL
  let : FiniteDimensional F L := hL.1
  have hcop : (finrank F E).Coprime (finrank F L) := hdegree ▸ hL.2.1
  refine hL.2.2.2.elim ?_
  intro hq hgen
  let : Fact (Irreducible (p.map (algebraMap F L))) := ⟨hq⟩
  dsimp only at hgen
  refine hgen.elim ?_
  intro c hc
  let M := AdjoinRoot (p.map (algebraMap F L))
  let jroot : AdjoinRoot p →+* M :=
    AdjoinRoot.map (algebraMap F L) p (p.map (algebraMap F L)) dvd_rfl
  let j : E →+* M := jroot.comp g.toRingHom
  let : Algebra E M := j.toAlgebra
  let : FiniteDimensional L M := (AdjoinRoot.powerBasis' (hpmonic.map _)).finite
  have : IsScalarTower F L M := inferInstance
  have hcoefficient (b : F) : j (algebraMap F E b) =
      algebraMap L M (algebraMap F L b) := by
    change jroot (g (algebraMap F E b)) = _
    rw [g.commutes]
    exact AdjoinRoot.map_of (algebraMap F L) p (p.map (algebraMap F L)) dvd_rfl b
  let : IsScalarTower F E M := IsScalarTower.of_algebraMap_eq fun b => (hcoefficient b).symm
  have hLM : finrank L M = finrank F E := by
    change finrank L (AdjoinRoot (p.map (algebraMap F L))) = _
    rw [(AdjoinRoot.powerBasis (hpmonic.map (algebraMap F L)).ne_zero).finrank,
      AdjoinRoot.powerBasis_dim, hpmonic.natDegree_map]
    exact hdegree
  have hmap : milnorKTheoryMap (algebraMap E M) (n + 1) x =
      milnorKTheoryMap jroot (n + 1) y := by
    exact DFunLike.congr_fun (milnorKTheoryMap_comp (n := n + 1) g.toRingHom jroot) x
  have hmixed : milnorKTheoryMap (algebraMap E M) (n + 1) x ∈
      milnorKMixedSpan (algebraMap L M) n := by
    change milnorKTheoryMap (algebraMap E M) (n + 1) x ∈ Submodule.span ℤ _
    exact Finsupp.mem_span_range_iff_exists_finsupp.mpr ⟨c, hc.trans hmap.symm⟩
  exact completePrime_of_coprime_mixed_field R S F E L M hp hcop hLM n x hmixed

end Complete

end Stacks.Chow

end
