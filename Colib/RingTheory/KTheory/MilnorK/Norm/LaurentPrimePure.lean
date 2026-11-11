/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.DVRPurePrimeComplete
public import Colib.RingTheory.KTheory.MilnorK.Norm.LaurentUnramified

import Colib.FieldTheory.AdjoinRoot.PurelyInseparable
import Mathlib.RingTheory.AdicCompletion.Completeness
import Colib.RingTheory.KTheory.MilnorK.Norm.PurePrimeEquivariance

/-!
# The Laurent norm-residue square for purely inseparable prime constants
-/

@[expose] public noncomputable section

open Polynomial IsLocalRing Module IntermediateField

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
  [IsPurelyInseparable k (AdjoinRoot (poly p))]

/-- Every Laurent class satisfies the actual norm-residue square for a purely inseparable
prime-degree constant extension. -/
theorem dvrMilnorTameSymbol'_milnorKNorm_laurentSeries_of_isPurelyInseparable
    (hp : d.Prime) (n : ℕ)
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
  let : IsAdicComplete (maximalIdeal (PowerSeries k)) (PowerSeries k) := by
    rw [PowerSeries.maximalIdeal_eq_span_X]
    infer_instance
  let : IsPurelyInseparable (LaurentSeries k)
      (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) :=
    AdjoinRoot.isPurelyInseparable_map_of_isPurelyInseparable (f := poly p)
  have hdegree : finrank (LaurentSeries k)
      (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) = d := by
    rw [AdjoinRoot.finrank_eq_natDegree ((monic p).map _),
      (monic p).natDegree_map, natDegree_eq p]
  exact dvrMilnorTameSymbol'_milnorKNorm_of_complete_of_isPurelyInseparable_of_prime
    (PowerSeries k) (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))
    (LaurentSeries k) (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k))))
    (hdegree.symm ▸ hp) n x

/-- The actual purely inseparable prime Laurent square returned to the original
constant fields through their residue equivalences. -/
theorem dvrMilnorTameSymbol'_milnorKNorm_laurentSeries_to_constants_of_isPurelyInseparable
    (hp : d.Prime) (m : ℕ)
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
  let S := AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k))
  let κ := ResidueField (PowerSeries k)
  let κS := ResidueField S
  let E := AdjoinRoot (poly p)
  let σ : κ ≃+* k := PowerSeries.residueFieldOfPowerSeries
  let τ : κS ≃+* E := AdjoinRoot.powerSeriesResidueEquiv (poly p)
  have hcoeff (a : κ) : τ (algebraMap κ κS a) = algebraMap k E (σ a) :=
    AdjoinRoot.powerSeriesResidueEquiv_algebraMap (poly p) a
  have hστ : τ.toRingHom.comp (algebraMap κ κS) =
      (algebraMap k E).comp σ.toRingHom := RingHom.ext hcoeff
  let : IsPurelyInseparable κ κS := by
    obtain ⟨q, _⟩ := ExpChar.exists k
    let : ExpChar κ q := RingHom.expChar σ.toRingHom σ.injective q
    apply (isPurelyInseparable_iff_pow_mem κ q).mpr
    intro a
    obtain ⟨r, b, hb⟩ := IsPurelyInseparable.pow_mem k q (τ a)
    refine ⟨r, σ.symm b, τ.injective ?_⟩
    calc
      τ (algebraMap κ κS (σ.symm b)) = algebraMap k E (σ (σ.symm b)) :=
        hcoeff (σ.symm b)
      _ = (τ a) ^ q ^ r := by simpa only [σ.apply_symm_apply] using hb
      _ = τ (a ^ q ^ r) := (map_pow τ _ _).symm
  have hdegree : finrank κ κS = d := by
    change finrank (ResidueField (PowerSeries k)) (ResidueField S) = d
    rw [AdjoinRoot.finrank_residueField_eq_natDegree ((monic p).map _)
      ((monic p).irreducible_map_powerSeries_C_residue (irreducible p)) (by
        rw [(monic p).natDegree_map]
        exact (irreducible p).natDegree_pos), (monic p).natDegree_map, natDegree_eq p]
  have hn (y : MilnorKTheory κS m) :
      milnorKTheoryMap σ.toRingHom m (milnorKNorm κ κS m y) =
        milnorKNorm k E m (milnorKTheoryMap τ.toRingHom m y) := by
    simp only [milnorKTheoryMap_eq_transport]
    exact milnorKNorm_map_ringEquiv_of_prime_of_isPurelyInseparable
      (hdegree.symm ▸ hp) σ τ hστ m y
  exact (congrArg (milnorKTheoryMap σ.toRingHom m)
    (dvrMilnorTameSymbol'_milnorKNorm_laurentSeries_of_isPurelyInseparable p hp m x)).trans (hn _)

end Stacks.Chow

end
