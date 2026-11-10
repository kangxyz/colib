/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.AuxiliaryMixedBranchErrorSeparable
public import Colib.RingTheory.KTheory.MilnorK.Norm.LaurentBranchRetraction
public import Colib.RingTheory.KTheory.MilnorK.Norm.LaurentResidueSeparable
public import Colib.RingTheory.KTheory.MilnorK.Norm.DVRPrimeAnnihilation
public import Colib.RingTheory.KTheory.MilnorK.FiniteMixedGenerationArbitrary
public import StacksFrontier.RingTheory.BaseChangeTransport
public import Mathlib.Data.Int.GCD

/-!
# The all-symbol Laurent square for separable normal prime constants

For each original class, finite mixed generation gives one actual coprime-degree
auxiliary field, which may be inseparable. The Japanese power-series base has
finite native normalization in that field. The original separable constant cover
has finite étale normalization at every actual auxiliary DVR and hence unramified
actual completed branches. The full weighted branch error retracts to the
auxiliary degree. Together with the original prime annihilator, Bezout gives the
chosen norm-residue square for every class. Neither degree is cancelled alone.

The final formula returns the actual residues to the original constant fields
using their existing coefficient-compatible equivalences. No auxiliary
separability, perfectness, characteristic restriction, additional norm-square
premise, alternate field model or chosen-norm tower identity is assumed.
-/

@[expose] public noncomputable section

open Polynomial IsLocalRing Module
open scoped TensorProduct

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree

attribute [local instance] Ideal.Quotient.field

attribute [local instance]
  Stacks.Chow.laurentUnramified_factMonic
  Stacks.Chow.laurentUnramified_factIrreducible
  Stacks.Chow.laurentUnramified_factIrreducibleLaurent
  Stacks.Chow.laurentUnramified_isDomain
  Stacks.Chow.laurentUnramified_isLocalRing
  Stacks.Chow.laurentUnramified_isDiscreteValuationRing
  Stacks.Chow.laurentUnramified_finitePowerSeries
  Stacks.Chow.laurentUnramified_torsionFreePowerSeries
  Stacks.Chow.laurentUnramified_isLocalHom
  Stacks.Chow.laurentUnramifiedAlgebra
  Stacks.Chow.laurentUnramified_isScalarTower
  Stacks.Chow.laurentUnramified_isFractionRing
  Stacks.Chow.laurentUnramified_finiteConstant
  Stacks.Chow.laurentUnramified_finiteLaurent

variable {k : Type u} [Field k] {d : ℕ} (p : MonicIrreducibleOfDegree k d)
  [Normal k (AdjoinRoot (poly p))]

/-- Every actual Laurent norm-residue error has a coprime auxiliary-degree
annihilator. All native normalization branches contribute to the degree sum. -/
theorem exists_coprime_smul_laurent_norm_residue_difference_eq_zero_of_separable
    (hsep : (poly p).Separable) (hp : d.Prime) (n : ℕ)
    (x : MilnorKTheory
      (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) (n + 1)) :
    ∃ a : ℕ, d.Coprime a ∧ (a : ℤ) •
      (dvrMilnorTameSymbol' (PowerSeries k) (LaurentSeries k) n
          (milnorKNorm (LaurentSeries k)
            (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) (n + 1) x) -
        milnorKNorm (ResidueField (PowerSeries k))
          (ResidueField (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))) n
          (dvrMilnorTameSymbol'
            (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))
            (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) n x)) = 0 := by
  classical
  let R := PowerSeries k
  let S := AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k))
  let F := LaurentSeries k
  let _ : SMul k F := Algebra.toSMul
  let _ : Module k F := Algebra.toModule
  have : IsScalarTower k R F :=
    IsScalarTower.of_algebraMap_eq' (R := k) (S := R) (A := F) rfl
  let q : F[X] := (poly p).map (algebraMap k F)
  let E := AdjoinRoot q
  have hqmonic : q.Monic := (monic p).map _
  have hqdegree : q.natDegree = d := ((monic p).natDegree_map _).trans (natDegree_eq p)
  let : Algebra.IsSeparable F E := isSeparable_laurentSeriesRoot p hsep
  let : IsSplittingField F E q := AdjoinRoot.isSplittingField_of_dvd_map (monic p) dvd_rfl
  let : Normal F E := Normal.of_isSplittingField q
  let : IsGalois F E :=
    { to_isSeparable := inferInstance, to_normal := inferInstance }
  let : Algebra.IsSeparable (ResidueField R) (ResidueField S) :=
    isSeparable_powerSeriesRoot_residue p hsep
  have hprime : Nat.Prime (finrank F E) := by
    rw [AdjoinRoot.finrank_eq_natDegree hqmonic, hqdegree]
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
  have : IsScalarTower R F K := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra k K := ((algebraMap R K).comp (algebraMap k R)).toAlgebra
  have : IsScalarTower k R K := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower k F K :=
    IsScalarTower.of_algebraMap_eq (R := k) (S := F) (A := K) fun a => by
      change algebraMap F K (algebraMap R F (algebraMap k R a)) = _
      rw [← IsScalarTower.algebraMap_apply k R F]
  let : Algebra R M := ((algebraMap K M).comp (algebraMap R K)).toAlgebra
  have : IsScalarTower R K M := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra S M := (j.comp (algebraMap S E)).toAlgebra
  have : IsScalarTower S E M := IsScalarTower.of_algebraMap_eq' rfl
  have hcoefficient (a : F) : j (algebraMap F E a) =
      algebraMap K M (algebraMap F K a) :=
    AdjoinRoot.map_of (algebraMap F K) q (q.map (algebraMap F K)) dvd_rfl a
  have : IsScalarTower R S M := IsScalarTower.of_algebraMap_eq fun r => by
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
    PowerSeries.isDedekindDomain_integralClosure_laurentSeries k K
  let : DecidableEq (Ideal (integralClosure R K)) := Classical.decEq _
  have hbranch :=
    ramification_smul_restrict_norm_residue_difference_eq_zero_of_separable_constant_cover
      k R S F E K M (poly p) (monic p) hsep econstant eta heta hprime n x hmixed
  refine ⟨finrank F K, hqdegree ▸ hcoprime, ?_⟩
  exact finrank_smul_eq_zero_of_laurent_integralClosure_branches k K n
    (dvrMilnorTameSymbol' R F n (milnorKNorm F E (n + 1) x) -
      milnorKNorm (ResidueField R) (ResidueField S) n (dvrMilnorTameSymbol' S E n x))
    hbranch

/-- The all-symbol actual Laurent norm-residue square for separable normal prime
constants, including prime degree equal to the characteristic. -/
theorem dvrMilnorTameSymbol'_milnorKNorm_laurentSeries_of_separable
    (hsep : (poly p).Separable) (hp : d.Prime) (n : ℕ)
    (x : MilnorKTheory
      (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) (n + 1)) :
    dvrMilnorTameSymbol' (PowerSeries k) (LaurentSeries k) n
        (milnorKNorm (LaurentSeries k)
          (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) (n + 1) x) =
      milnorKNorm (ResidueField (PowerSeries k))
        (ResidueField (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))) n
        (dvrMilnorTameSymbol'
          (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))
          (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) n x) := by
  let : Algebra.IsSeparable (LaurentSeries k)
      (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) :=
    isSeparable_laurentSeriesRoot p hsep
  let : IsSplittingField (LaurentSeries k)
      (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k))))
      ((poly p).map (algebraMap k (LaurentSeries k))) :=
    AdjoinRoot.isSplittingField_of_dvd_map (monic p) dvd_rfl
  let : Normal (LaurentSeries k)
      (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) :=
    Normal.of_isSplittingField ((poly p).map (algebraMap k (LaurentSeries k)))
  let : IsGalois (LaurentSeries k)
      (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) :=
    { to_isSeparable := inferInstance, to_normal := inferInstance }
  have hdegree : finrank (LaurentSeries k)
      (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) = d := by
    rw [AdjoinRoot.finrank_eq_natDegree ((monic p).map _),
      (monic p).natDegree_map, natDegree_eq p]
  obtain ⟨a, hcoprime, ha⟩ :=
    exists_coprime_smul_laurent_norm_residue_difference_eq_zero_of_separable p hsep hp n x
  have hell := finrank_smul_norm_residue_difference_eq_zero
    (PowerSeries k) (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))
    (LaurentSeries k) (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k))))
    (hdegree.symm ▸ hp) n x
  rw [hdegree] at hell
  apply sub_eq_zero.mp
  have h := intGCD_nsmul_eq_zero.mpr ⟨hell, ha⟩
  simpa only [Int.gcd_natCast_natCast, hcoprime.gcd_eq_one, one_nsmul] using h

/-- The all-symbol separable normal-prime Laurent square returned to the
original constant fields through the actual residue equivalences. -/
theorem dvrMilnorTameSymbol'_milnorKNorm_laurentSeries_to_constants_of_separable
    (hsep : (poly p).Separable) (hp : d.Prime) (m : ℕ)
    (x : MilnorKTheory
      (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) (m + 1)) :
    milnorKTheoryMap PowerSeries.residueFieldOfPowerSeries.toRingHom m
        (dvrMilnorTameSymbol' (PowerSeries k) (LaurentSeries k) m
          (milnorKNorm (LaurentSeries k)
            (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) (m + 1) x)) =
      milnorKNorm k (AdjoinRoot (poly p)) m
        (milnorKTheoryMap (AdjoinRoot.powerSeriesResidueEquiv (poly p)).toRingHom m
          (dvrMilnorTameSymbol'
            (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))
            (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) m x)) := by
  have hmono := dvrMilnorTameSymbol'_milnorKNorm_laurentSeries_of_separable p hsep hp m x
  calc
    _ = milnorKTheoryMap PowerSeries.residueFieldOfPowerSeries.toRingHom m
        (milnorKNorm (ResidueField (PowerSeries k))
          (ResidueField (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))) m
          (dvrMilnorTameSymbol'
            (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))
            (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) m x)) :=
      congrArg (milnorKTheoryMap PowerSeries.residueFieldOfPowerSeries.toRingHom m) hmono
    _ = _ := milnorKNorm_powerSeriesResidueEquiv_of_separable p hsep hp m _

end Stacks.Chow

end
