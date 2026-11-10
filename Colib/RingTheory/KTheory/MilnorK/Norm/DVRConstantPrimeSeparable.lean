/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.IntegralClosure.JapaneseDVR
public import Colib.RingTheory.KTheory.MilnorK.Norm.AuxiliaryMixedBranchErrorSeparable
public import Colib.RingTheory.KTheory.MilnorK.Norm.BranchNormRetraction
public import Colib.RingTheory.KTheory.MilnorK.Norm.DVRPrimeAnnihilation
public import Colib.RingTheory.KTheory.MilnorK.FiniteMixedGenerationArbitrary
public import Colib.FieldTheory.AdjoinRoot.NormalScalar
public import Colib.FieldTheory.AdjoinRoot.Separable
public import StacksFrontier.RingTheory.BaseChangeTransport

/-!
# All-symbol norm and residue for finite local constant covers of Japanese DVRs

The actual generic field is the literal coefficient extension of the original
separable normal prime polynomial. Finite mixed generation supplies an auxiliary
field of coprime degree, without assuming auxiliary separability. Japanese
normalization and every actual completed branch give one annihilator; the prime
trace gives the other. Bezout proves the actual norm-residue square.

The source ring S is required to be a finite local DVR over R. In a split
polynomial-point cover, localizing a single branch does not provide that finite
instance. A separate split-branch argument is still required for the complete
finite-point sum. No coefficient-field section of R or its completion is used.
-/

@[expose] public noncomputable section

open Polynomial IsLocalRing Module
open scoped TensorProduct

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree

attribute [local instance] Ideal.Quotient.field

variable (k R S F : Type u)
  [Field k]
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Algebra k R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
  [IsLocalHom (algebraMap R S)]
  [Field F] [Algebra R F] [IsFractionRing R F]
  [Algebra k F] [IsScalarTower k R F]
  {d : ℕ} (p : MonicIrreducibleOfDegree k d)

local instance japaneseConstantCover_nativeIrreducible : Fact (Irreducible (poly p)) :=
  ⟨irreducible p⟩

variable [Normal k (AdjoinRoot (poly p))]
  [Fact (Irreducible ((poly p).map (algebraMap k F)))]
  [Algebra S (AdjoinRoot ((poly p).map (algebraMap k F)))]
  [IsFractionRing S (AdjoinRoot ((poly p).map (algebraMap k F)))]
  [IsScalarTower R S (AdjoinRoot ((poly p).map (algebraMap k F)))]
  [Algebra.IsSeparable (ResidueField R) (ResidueField S)]

local instance japaneseConstantCover_genericFinite :
    Module.Finite F (AdjoinRoot ((poly p).map (algebraMap k F))) :=
  ((monic p).map _).finite_adjoinRoot

set_option backward.isDefEq.respectTransparency false in
/-- Every error for an actual finite local constant cover of a Japanese DVR
has a coprime auxiliary-degree annihilator. Every normalization branch is retained. -/
theorem exists_coprime_smul_norm_residue_difference_eq_zero_of_japanese_constant_cover
    (hR : IsJapaneseRing R) (hsep : (poly p).Separable) (hp : d.Prime) (n : ℕ)
    (x : MilnorKTheory
      (AdjoinRoot ((poly p).map (algebraMap k F))) (n + 1)) :
    ∃ a : ℕ, d.Coprime a ∧ (a : ℤ) •
      (dvrMilnorTameSymbol' R F n
          (milnorKNorm F
            (AdjoinRoot ((poly p).map (algebraMap k F))) (n + 1) x) -
        milnorKNorm (ResidueField R)
          (ResidueField S) n
          (dvrMilnorTameSymbol'
            S
            (AdjoinRoot ((poly p).map (algebraMap k F))) n x)) = 0 := by
  classical
  let q : F[X] := (poly p).map (algebraMap k F)
  let E := AdjoinRoot q
  have hqmonic : q.Monic := (monic p).map _
  have hqdegree : q.natDegree = d := ((monic p).natDegree_map _).trans (natDegree_eq p)
  let : Algebra.IsSeparable F E := AdjoinRoot.isSeparable_of_polynomial_separable _ hsep.map
  let : IsSplittingField F E q := AdjoinRoot.isSplittingField_of_dvd_map (monic p) dvd_rfl
  let : Normal F E := Normal.of_isSplittingField q
  let : IsGalois F E :=
    { to_isSeparable := inferInstance, to_normal := inferInstance }
  have hprime : Nat.Prime (finrank F E) := by
    rw [(AdjoinRoot.powerBasis hqmonic.ne_zero).finrank, AdjoinRoot.powerBasis_dim,
      hqdegree]
    exact hp
  obtain ⟨s, _hs, K, hfinite, hcoprime, _hsplit, hq, hgen⟩ :=
    exists_finite_coprime_milnorK_mixed_expansion_arbitrary q hqmonic
      (hqdegree.symm ▸ hp) n x
  let : FiniteDimensional F K := hfinite
  let : Fact (Irreducible (q.map (algebraMap F K))) := ⟨hq⟩
  dsimp only at hgen
  obtain ⟨c, hc⟩ := hgen
  let M := AdjoinRoot (q.map (algebraMap F K))
  let j : E →+* M := AdjoinRoot.map (algebraMap F K) q
    (q.map (algebraMap F K)) dvd_rfl
  let : Algebra E M := j.toAlgebra
  let : FiniteDimensional K M := (AdjoinRoot.powerBasis' (hqmonic.map _)).finite
  let : Algebra.IsSeparable K M :=
    AdjoinRoot.isSeparable_of_polynomial_separable _ hsep.map.map
  let : Algebra R K := ((algebraMap F K).comp (algebraMap R F)).toAlgebra
  let _ : SMul R K := Algebra.toSMul
  let _ : Module R K := Algebra.toModule
  have : IsScalarTower R F K :=
    IsScalarTower.of_algebraMap_eq' (R := R) (S := F) (A := K) rfl
  let : Algebra k K := ((algebraMap R K).comp (algebraMap k R)).toAlgebra
  have : IsScalarTower k R K :=
    IsScalarTower.of_algebraMap_eq' (R := k) (S := R) (A := K) rfl
  have : IsScalarTower k F K :=
    IsScalarTower.of_algebraMap_eq (R := k) (S := F) (A := K) fun a => by
      change algebraMap F K (algebraMap R F (algebraMap k R a)) = _
      rw [← IsScalarTower.algebraMap_apply k R F]
  let : Algebra R M := ((algebraMap K M).comp (algebraMap R K)).toAlgebra
  let _ : SMul R M := Algebra.toSMul
  let _ : Module R M := Algebra.toModule
  have : IsScalarTower R K M :=
    IsScalarTower.of_algebraMap_eq' (R := R) (S := K) (A := M) rfl
  let : Algebra S M := (j.comp (algebraMap S E)).toAlgebra
  have : IsScalarTower S E M :=
    IsScalarTower.of_algebraMap_eq' (R := S) (S := E) (A := M) rfl
  have hcoefficient (a : F) : j (algebraMap F E a) =
      algebraMap K M (algebraMap F K a) :=
    AdjoinRoot.map_of (algebraMap F K) q (q.map (algebraMap F K)) dvd_rfl a
  have : IsScalarTower R S M :=
    IsScalarTower.of_algebraMap_eq (R := R) (S := S) (A := M) fun r => by
      change algebraMap K M (algebraMap F K (algebraMap R F r)) =
        j (algebraMap S E (algebraMap R S r))
      rw [← IsScalarTower.algebraMap_apply R S E, IsScalarTower.algebraMap_apply R F E]
      exact (hcoefficient (algebraMap R F r)).symm
  let eta : K ⊗[F] E ≃ₐ[K] M := AdjoinRoot.baseChangeAlgEquiv F K q
  have heta (e : E) : eta (1 ⊗ₜ[F] e) = algebraMap E M e := by
    have hmap : eta.toRingHom.comp
        (Algebra.TensorProduct.includeRight : E →ₐ[F] K ⊗[F] E).toRingHom = j := by
      apply AdjoinRoot.ringHom_ext
      · apply RingHom.ext
        intro a
        exact (AdjoinRoot.baseChangeAlgEquiv_tmul_of F K q a).trans
          (AdjoinRoot.map_of (algebraMap F K) q (q.map (algebraMap F K)) dvd_rfl a).symm
      · exact (AdjoinRoot.baseChangeAlgEquiv_tmul_root F K q).trans
          (AdjoinRoot.map_root (algebraMap F K) q (q.map (algebraMap F K)) dvd_rfl).symm
    exact RingHom.congr_fun hmap e
  have hmixed : milnorKTheoryMap (algebraMap E M) (n + 1) x ∈
      milnorKMixedSpan (algebraMap K M) n := by
    change milnorKTheoryMap j (n + 1) x ∈ Submodule.span ℤ _
    exact Finsupp.mem_span_range_iff_exists_finsupp.mpr ⟨c, hc⟩
  have hpoly : (poly p).map (algebraMap k K) = q.map (algebraMap F K) := by
    dsimp only [q]
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq k F K]
  let econstant : AdjoinRoot ((poly p).map (algebraMap k K)) ≃ₐ[K] M :=
    AdjoinRoot.algEquivOfEq K _ _ hpoly
  let : IsDedekindDomain (integralClosure R K) :=
    IsDiscreteValuationRing.isDedekindDomain_integralClosure_of_isJapaneseRing R hR F K
  let : DecidableEq (Ideal (integralClosure R K)) := Classical.decEq _
  have hbranch :=
    ramification_smul_restrict_norm_residue_difference_eq_zero_of_separable_constant_cover
      k R S F E K M (poly p) (monic p) hsep econstant eta heta hprime n x hmixed
  refine ⟨finrank F K, hqdegree ▸ hcoprime, ?_⟩
  let : Module.Finite R (integralClosure R K) :=
    module_finite_integralClosure_of_isJapaneseRing hR F K
  let : Module.IsTorsionFree R K := by
    apply isTorsionFree_iff_algebraMap_injective.mpr
    change Function.Injective ((algebraMap F K).comp (algebraMap R F))
    exact (algebraMap F K).injective.comp (IsFractionRing.injective R F)
  let : Module.IsTorsionFree R (integralClosure R K) :=
    IsIntegralClosure.isTorsionFree (A := integralClosure R K) R K
  let : IsFractionRing (integralClosure R K) K :=
    integralClosure.isFractionRing_of_finite_extension F K
  exact finrank_smul_eq_zero_of_branchCompletion_ramification_smul_restrict_eq_zero
    R (integralClosure R K) F K n
    (dvrMilnorTameSymbol' R F n (milnorKNorm F E (n + 1) x) -
      milnorKNorm (ResidueField R) (ResidueField S) n (dvrMilnorTameSymbol' S E n x))
    hbranch

/-- The all-symbol norm-residue square for an actual finite local constant cover
of a Japanese DVR. The prime degree may equal the characteristic. -/
theorem dvrMilnorTameSymbol'_milnorKNorm_of_japanese_separable_constant_cover
    (hR : IsJapaneseRing R) (hsep : (poly p).Separable) (hp : d.Prime) (n : ℕ)
    (x : MilnorKTheory
      (AdjoinRoot ((poly p).map (algebraMap k F))) (n + 1)) :
    dvrMilnorTameSymbol' R F n
        (milnorKNorm F
          (AdjoinRoot ((poly p).map (algebraMap k F))) (n + 1) x) =
      milnorKNorm (ResidueField R)
        (ResidueField S) n
        (dvrMilnorTameSymbol'
          S
          (AdjoinRoot ((poly p).map (algebraMap k F))) n x) := by
  let : Algebra.IsSeparable F
      (AdjoinRoot ((poly p).map (algebraMap k F))) :=
    AdjoinRoot.isSeparable_of_polynomial_separable _ hsep.map
  let : IsSplittingField F
      (AdjoinRoot ((poly p).map (algebraMap k F)))
      ((poly p).map (algebraMap k F)) :=
    AdjoinRoot.isSplittingField_of_dvd_map (monic p) dvd_rfl
  let : Normal F
      (AdjoinRoot ((poly p).map (algebraMap k F))) :=
    Normal.of_isSplittingField ((poly p).map (algebraMap k F))
  let : IsGalois F
      (AdjoinRoot ((poly p).map (algebraMap k F))) :=
    { to_isSeparable := inferInstance, to_normal := inferInstance }
  have hdegree : finrank F
      (AdjoinRoot ((poly p).map (algebraMap k F))) = d := by
    rw [(AdjoinRoot.powerBasis (((monic p).map (algebraMap k F)).ne_zero)).finrank,
      AdjoinRoot.powerBasis_dim, (monic p).natDegree_map, natDegree_eq p]
  obtain ⟨a, hcoprime, ha⟩ :=
    exists_coprime_smul_norm_residue_difference_eq_zero_of_japanese_constant_cover
      k R S F p hR hsep hp n x
  have hell := finrank_smul_norm_residue_difference_eq_zero
    R S
    F (AdjoinRoot ((poly p).map (algebraMap k F)))
    (hdegree.symm ▸ hp) n x
  rw [hdegree] at hell
  apply sub_eq_zero.mp
  have h := intGCD_nsmul_eq_zero.mpr ⟨hell, ha⟩
  simpa only [Int.gcd_natCast_natCast, hcoprime.gcd_eq_one, one_nsmul] using h

end Stacks.Chow

end
