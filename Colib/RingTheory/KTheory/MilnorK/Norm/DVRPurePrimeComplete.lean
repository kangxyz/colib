/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.DVRPurePrimeCoprimeDescent
public import Colib.RingTheory.IntegralClosure.IntermediateTower
public import Colib.RingTheory.DiscreteValuationRing.CompleteExtension
public import Colib.RingTheory.KTheory.MilnorK.FiniteMixedGenerationArbitrary
public import Colib.Util.References
public import StacksFrontier.RingTheory.BaseChangeTransport

/-!
# Norm and tame residue in purely inseparable prime degree

For a fixed class, a finite coefficient extension of coprime degree gives
a mixed-symbol expansion. Finite separable normalization over each of the
two original DVRs supplies the auxiliary local square. The coprime
calculation then proves equality for the original chosen norm and residue.
-/

@[expose] public noncomputable section

open IsLocalRing Module Polynomial IntermediateField
open scoped TensorProduct

universe u

namespace Stacks.Chow

private theorem isSeparable_of_coprime_expChar
    (F L : Type u) [Field F] [Field L] [Algebra F L] [FiniteDimensional F L]
    (p : ℕ) [ExpChar F p] (hp : p.Prime) (hcop : p.Coprime (finrank F L)) :
    Algebra.IsSeparable F L := by
  apply (isSeparable_iff_finInsepDegree_eq_one F L).mpr
  obtain ⟨n, hn⟩ := finInsepDegree_eq_pow F L p
  have hi : Field.finInsepDegree F L ∣ finrank F L :=
    ⟨Field.finSepDegree F L, by
      simpa only [Nat.mul_comm] using (Field.finSepDegree_mul_finInsepDegree F L).symm⟩
  have hnzero : n = 0 := by
    by_contra h
    have hdiv : p ∣ Field.finInsepDegree F L := by
      rw [hn]
      exact dvd_pow_self p h
    exact (hp.coprime_iff_not_dvd.mp hcop) (dvd_trans hdiv hi)
  simpa only [hnzero, pow_zero] using hn

private theorem isPurelyInseparable_of_tensor_field_equiv
    (F E L M : Type u) [Field F] [Field E] [Field L] [Field M]
    [Algebra F E] [Algebra F L] [Algebra L M] [IsPurelyInseparable F E]
    (η : L ⊗[F] E ≃ₐ[L] M) : IsPurelyInseparable L M := by
  let q := ringExpChar F
  let : ExpChar L q := expChar_of_injective_algebraMap (algebraMap F L).injective q
  apply (isPurelyInseparable_iff_pow_mem L q).mpr
  intro z
  obtain ⟨n, b, hb⟩ :=
    IsPurelyInseparable.exists_pow_pow_mem_range_tensorProduct_of_expChar
      (k := F) (K := E) (R := L) q (η.symm z)
  refine ⟨n, b, ?_⟩
  have h := congrArg η hb
  simpa only [map_pow, η.commutes, η.apply_symm_apply] using h

/-- An actual finite coprime mixed field square supplies the required DVR
normalizations over the complete base. The upper integral closure is taken
over the original supplied DVR, where the auxiliary extension is separable. -/
private theorem dvr_norm_residue_of_coprime_mixed_field
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
    [IsPurelyInseparable F E] [IsPurelyInseparable L M]
    (hp : Nat.Prime (finrank F E)) (hcop : (finrank F E).Coprime (finrank F L))
    (hLM : finrank L M = finrank F E) (n : ℕ) (x : MilnorKTheory E (n + 1))
    (hmixed : milnorKTheoryMap (algebraMap E M) (n + 1) x ∈
      milnorKMixedSpan (algebraMap L M) n) :
    dvrMilnorTameSymbol' R F n (milnorKNorm F E (n + 1) x) =
      milnorKNorm (ResidueField R) (ResidueField S) n (dvrMilnorTameSymbol' S E n x) := by
  classical
  let : FiniteDimensional F M := Module.Finite.trans L M
  let : FiniteDimensional E M := Module.Finite.of_restrictScalars_finite F E M
  let : Module.Free F L := Module.Free.of_divisionRing F L
  let : Module.Free L M := Module.Free.of_divisionRing L M
  let : Module.Free E M := Module.Free.of_divisionRing E M
  have hEM : finrank E M = finrank F L := mul_left_cancel₀ hp.ne_zero (by
    have h := (finrank_mul_finrank F E M).trans (finrank_mul_finrank F L M).symm
    simpa only [hLM, Nat.mul_comm (finrank F L) (finrank F E)] using h)
  obtain ⟨r, hr⟩ := IsPurelyInseparable.finrank_eq_pow F E (ringExpChar F)
  have hchar : ringExpChar F = finrank F E := (hp.pow_eq_iff.mp hr.symm).1
  let : ExpChar F (finrank F E) := hchar ▸ inferInstance
  let : ExpChar E (finrank F E) :=
    expChar_of_injective_algebraMap (algebraMap F E).injective _
  let : Algebra.IsSeparable F L := isSeparable_of_coprime_expChar F L _ hp hcop
  let : Algebra.IsSeparable E M := isSeparable_of_coprime_expChar E M _ hp
    (by simpa only [hEM] using hcop)
  let : Algebra R L := ((algebraMap F L).comp (algebraMap R F)).toAlgebra
  have : IsScalarTower R F L := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra R M := ((algebraMap L M).comp (algebraMap R L)).toAlgebra
  have : IsScalarTower R L M := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R F M := IsScalarTower.of_algebraMap_eq fun b =>
    (IsScalarTower.algebraMap_apply F L M (algebraMap R F b)).symm
  let : Algebra S M := ((algebraMap E M).comp (algebraMap S E)).toAlgebra
  have : IsScalarTower S E M := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R S M := IsScalarTower.of_algebraMap_eq fun b => by
    change algebraMap R M b = algebraMap E M (algebraMap S E (algebraMap R S b))
    rw [← IsScalarTower.algebraMap_apply R S E,
      IsScalarTower.algebraMap_apply R F E,
      ← IsScalarTower.algebraMap_apply F E M,
      ← IsScalarTower.algebraMap_apply R F M]
  let : Module.IsTorsionFree R L := by
    apply Module.isTorsionFree_iff_algebraMap_injective.mpr
    change Function.Injective ((algebraMap F L).comp (algebraMap R F))
    exact (algebraMap F L).injective.comp (IsFractionRing.injective R F)
  let : Module.IsTorsionFree S M := by
    apply Module.isTorsionFree_iff_algebraMap_injective.mpr
    change Function.Injective ((algebraMap E M).comp (algebraMap S E))
    exact (algebraMap E M).injective.comp (IsFractionRing.injective S E)
  let T := integralClosure R L
  let U := integralClosure S M
  let : IsDiscreteValuationRing T :=
    IsDiscreteValuationRing.CompleteExtension.integralClosure_isDiscreteValuationRing R F L
  let : IsLocalHom (algebraMap R T) :=
    IsDiscreteValuationRing.CompleteExtension.integralClosure_isLocalHom R F L
  let : IsFractionRing T L :=
    IsIntegralClosure.isFractionRing_of_finite_extension R F L T
  let : Module.Finite R T := IsIntegralClosure.finite R F L T
  let : Module.IsTorsionFree R T := IsIntegralClosure.isTorsionFree R L
  let : Module.Finite S U := IsIntegralClosure.finite S E M U
  let : Algebra R U := ((algebraMap S U).comp (algebraMap R S)).toAlgebra
  have : IsScalarTower R S U := IsScalarTower.of_algebraMap_eq' rfl
  let : Module.Finite R U := Module.Finite.trans S U
  let : IsLocalRing U := IsDiscreteValuationRing.CompleteExtension.isLocalRing_of_finite R U
  let : IsDedekindDomain U := integralClosure.isDedekindDomain S E M
  let : IsFractionRing U M := IsIntegralClosure.isFractionRing_of_finite_extension S E M U
  have hinj : Function.Injective (algebraMap S U) :=
    IsDiscreteValuationRing.CompleteExtension.integralClosure_algebraMap_injective S E M
  have hnf : ¬IsField U := fun h => IsDiscreteValuationRing.not_isField S
    (isField_of_isIntegral_of_isField hinj h)
  let : IsDiscreteValuationRing U := ((IsDiscreteValuationRing.TFAE U hnf).out 1 3).mpr
    (show IsDedekindDomain U from inferInstance)
  let : Module.IsTorsionFree S U := IsIntegralClosure.isTorsionFree S M
  let : IsLocalHom (algebraMap S U) :=
    IsDiscreteValuationRing.CompleteExtension.integralClosure_isLocalHom S E M
  have : IsScalarTower R U M := IsScalarTower.of_algebraMap_eq fun b => by
    change algebraMap R M b = algebraMap U M (algebraMap S U (algebraMap R S b))
    exact (IsScalarTower.algebraMap_apply R S M b).trans
      (IsScalarTower.algebraMap_apply S U M (algebraMap R S b))
  let : IsIntegralClosure U R M := IsIntegralClosure.of_isIntegrallyClosed U R M
  let : Algebra T U := IsIntegralClosure.IntermediateTower.closureAlgebra R U L M
  have : IsScalarTower R T U := IsIntegralClosure.IntermediateTower.baseTower R U L M
  have : IsScalarTower T L M := inferInstance
  have : IsScalarTower T U M := IsIntegralClosure.IntermediateTower.topTower R U L M
  let : IsIntegralClosure U T M :=
    IsIntegralClosure.IntermediateTower.upper_isIntegralClosure R U L M
  let : Module.IsTorsionFree T M := by
    apply Module.isTorsionFree_iff_algebraMap_injective.mpr
    change Function.Injective ((algebraMap L M).comp (algebraMap T L))
    exact (algebraMap L M).injective.comp (IsFractionRing.injective T L)
  let : Module.Finite T U := IsIntegralClosure.IntermediateTower.upper_finite R U L M
  let : Module.IsTorsionFree T U := IsIntegralClosure.isTorsionFree T M
  let : IsLocalHom (algebraMap T U) :=
    IsIntegralClosure.IntermediateTower.upper_isLocalHom R U L M
  exact dvrMilnorTameSymbol'_milnorKNorm_of_coprime_pure_prime_square
    R S T U F E L M hp hcop hLM n x hmixed

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
  [FiniteDimensional F E] [IsPurelyInseparable F E]

/-- All classes in a purely inseparable prime-degree finite
local extension over a complete DVR satisfy the native norm-residue square. -/
@[colib_tag "COL-1024",
  colib_ref "axiom_stacks_5ed82d14"
    "StacksFrontier/RingTheory/DiscreteValuationRing/FundamentalIdentity.lean:33-52" "ingredient"
    "The local ramification index times the residue degree gives the fraction-field degree"]
theorem dvrMilnorTameSymbol'_milnorKNorm_of_complete_of_isPurelyInseparable_of_prime
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
  let g : E ≃ₐ[F] AdjoinRoot p :=
    { toRingEquiv := e.toRingEquiv
      commutes' := e.commutes }
  let y : MilnorKTheory (AdjoinRoot p) (n + 1) :=
    milnorKTheoryMap g.toRingHom (n + 1) x
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
  have : IsScalarTower F E M :=
    IsScalarTower.of_algebraMap_eq fun b => (hcoefficient b).symm
  have hLM : finrank L M = finrank F E := by
    change finrank L (AdjoinRoot (p.map (algebraMap F L))) = _
    rw [(AdjoinRoot.powerBasis (hpmonic.map (algebraMap F L)).ne_zero).finrank,
      AdjoinRoot.powerBasis_dim, hpmonic.natDegree_map]
    exact hdegree
  let η : L ⊗[F] E ≃ₐ[L] M :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L) g).trans
      (AdjoinRoot.baseChangeAlgEquiv F L p)
  let : IsPurelyInseparable L M := isPurelyInseparable_of_tensor_field_equiv F E L M η
  have hmap : milnorKTheoryMap (algebraMap E M) (n + 1) x =
      milnorKTheoryMap jroot (n + 1) y := by
    exact DFunLike.congr_fun (milnorKTheoryMap_comp (n := n + 1) g.toRingHom jroot) x
  have hmixed : milnorKTheoryMap (algebraMap E M) (n + 1) x ∈
      milnorKMixedSpan (algebraMap L M) n := by
    change milnorKTheoryMap (algebraMap E M) (n + 1) x ∈ Submodule.span ℤ _
    exact Finsupp.mem_span_range_iff_exists_finsupp.mpr ⟨c, hc.trans hmap.symm⟩
  exact dvr_norm_residue_of_coprime_mixed_field R S F E L M hp hcop hLM n x hmixed

end Complete

end Stacks.Chow

end
