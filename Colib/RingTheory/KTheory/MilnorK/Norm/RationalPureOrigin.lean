/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.RationalPureCompletion
public import Colib.RingTheory.KTheory.MilnorK.Norm.LaurentPrimePure
public import Colib.RingTheory.KTheory.MilnorK.Residue.CanonicalRamifiedMap
public import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.InfinityResidue

/-!
# Origin and infinity residues in purely inseparable prime degree

The complete-DVR square gives the origin square after the actual rational
and residue maps. The original chart inversion gives the infinity square.
-/

@[expose] public noncomputable section

open Polynomial IsLocalRing Module
open scoped RatFunc
attribute [local instance] Polynomial.algebra Ideal.Quotient.field

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree

variable {k : Type u} [Field k]

private theorem powerSeriesX_mem_maximalIdeal :
    (PowerSeries.X : PowerSeries k) ∈ maximalIdeal (PowerSeries k) :=
  PowerSeries.X_irreducible.not_isUnit

private def originToPowerSeriesBase (k : Type u) [Field k] :
    localRingAtOrigin k →+* PowerSeries k :=
  Polynomial.localizeAtOriginEval₂ (PowerSeries.C : k →+* PowerSeries k)
    (powerSeriesX_mem_maximalIdeal (k := k))

private instance : IsLocalHom (originToPowerSeriesBase k) :=
  Polynomial.isLocalHom_localizeAtOriginEval₂ _ _

private theorem originToPowerSeriesBase_generic_square :
    (algebraMap (RatFunc k) (LaurentSeries k)).comp
        (algebraMap (localRingAtOrigin k) (RatFunc k)) =
      (algebraMap (PowerSeries k) (LaurentSeries k)).comp
        (originToPowerSeriesBase k) := by
  apply IsLocalization.ringHom_ext (Ideal.span ({X} : Set k[X])).primeCompl
  apply Polynomial.ringHom_ext
  · intro a
    change algebraMap (RatFunc k) (LaurentSeries k)
        (algebraMap (localRingAtOrigin k) (RatFunc k)
          (algebraMap k[X] (localRingAtOrigin k) (C a))) =
      algebraMap (PowerSeries k) (LaurentSeries k)
        (Polynomial.localizeAtOriginEval₂ (PowerSeries.C : k →+* PowerSeries k)
          (powerSeriesX_mem_maximalIdeal (k := k))
          (algebraMap k[X] (localRingAtOrigin k) (C a)))
    rw [← IsScalarTower.algebraMap_apply k[X] (localRingAtOrigin k) (RatFunc k),
      RatFunc.algebraMap_C, Polynomial.localizeAtOriginEval₂_algebraMap,
      Polynomial.eval₂_C]
    exact RingHom.congr_fun RatFunc.algebraMap_laurentSeries_comp_C a
  · change algebraMap (RatFunc k) (LaurentSeries k)
        (algebraMap (localRingAtOrigin k) (RatFunc k)
          (algebraMap k[X] (localRingAtOrigin k) X)) =
      algebraMap (PowerSeries k) (LaurentSeries k)
        (Polynomial.localizeAtOriginEval₂ (PowerSeries.C : k →+* PowerSeries k)
          (powerSeriesX_mem_maximalIdeal (k := k))
          (algebraMap k[X] (localRingAtOrigin k) X))
    rw [← IsScalarTower.algebraMap_apply k[X] (localRingAtOrigin k) (RatFunc k),
      RatFunc.algebraMap_X, Polynomial.localizeAtOriginEval₂_X]
    change ((RatFunc.X : RatFunc k) : LaurentSeries k) =
      ((PowerSeries.X : PowerSeries k) : LaurentSeries k)
    rw [RatFunc.coe_X, PowerSeries.coe_X]

private theorem originToPowerSeriesBase_residue_square :
    PowerSeries.residueFieldOfPowerSeries.toRingHom.comp
        (ResidueField.map (originToPowerSeriesBase k)) =
      (residueFieldAtOriginEquiv k).symm.toRingHom := by
  apply RingHom.ext
  intro z
  obtain ⟨a, rfl⟩ := (residueFieldAtOriginEquiv k).surjective z
  change PowerSeries.residueFieldOfPowerSeries
      (ResidueField.map (originToPowerSeriesBase k)
        (residue (localRingAtOrigin k)
          (algebraMap k[X] (localRingAtOrigin k) (C a)))) =
    (residueFieldAtOriginEquiv k).symm (residueFieldAtOriginEquiv k a)
  rw [RingEquiv.symm_apply_apply, ResidueField.map_residue]
  change PowerSeries.residueFieldOfPowerSeries
      (residue (PowerSeries k)
        (Polynomial.localizeAtOriginEval₂ (PowerSeries.C : k →+* PowerSeries k)
          (powerSeriesX_mem_maximalIdeal (k := k))
          (algebraMap k[X] (localRingAtOrigin k) (C a)))) = a
  rw [Polynomial.localizeAtOriginEval₂_algebraMap, Polynomial.eval₂_C]
  change PowerSeries.constantCoeff (PowerSeries.C a) = a
  simp

private theorem dvrMilnorTameSymbol'_ratFunc_map_laurentSeries (n : ℕ)
    (x : MilnorKTheory (RatFunc k) (n + 1)) :
    milnorKTheoryMap PowerSeries.residueFieldOfPowerSeries.toRingHom n
        (dvrMilnorTameSymbol' (PowerSeries k) (LaurentSeries k) n
          (milnorKTheoryMap (algebraMap (RatFunc k) (LaurentSeries k)) (n + 1) x)) =
      milnorKTheoryMap (residueFieldAtOriginEquiv k).symm.toRingHom n
        (dvrMilnorTameSymbol' (localRingAtOrigin k) (RatFunc k) n x) := by
  have hf : ∀ a : localRingAtOrigin k,
      algebraMap (RatFunc k) (LaurentSeries k)
          (algebraMap (localRingAtOrigin k) (RatFunc k) a) =
        algebraMap (PowerSeries k) (LaurentSeries k) (originToPowerSeriesBase k a) :=
    fun a => RingHom.congr_fun originToPowerSeriesBase_generic_square a
  have hπ : Irreducible (originToPowerSeriesBase k
      (algebraMap k[X] (localRingAtOrigin k) X)) := by
    change Irreducible
      (Polynomial.localizeAtOriginEval₂ (PowerSeries.C : k →+* PowerSeries k)
        (powerSeriesX_mem_maximalIdeal (k := k))
        (algebraMap k[X] (localRingAtOrigin k) X))
    rw [Polynomial.localizeAtOriginEval₂_X]
    exact PowerSeries.X_irreducible
  have h := DFunLike.congr_fun
    (dvrMilnorTameSymbol'_map_ramified (originToPowerSeriesBase k)
      (algebraMap (RatFunc k) (LaurentSeries k)) hf
      (irreducible_algebraMap_X (k := k)) hπ (1 : (PowerSeries k)ˣ) 1
      (by simp) n) x
  simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
    Nat.cast_one, one_smul] at h
  rw [h]
  change ((milnorKTheoryMap PowerSeries.residueFieldOfPowerSeries.toRingHom n).comp
    (milnorKTheoryMap (ResidueField.map (originToPowerSeriesBase k)) n))
      (dvrMilnorTameSymbol' (localRingAtOrigin k) (RatFunc k) n x) = _
  rw [← milnorKTheoryMap_comp, originToPowerSeriesBase_residue_square]

private theorem infinityResidue_eq_origin_chartInversion (n : ℕ)
    (x : MilnorKTheory (RatFunc k) (n + 1)) :
    infinityResidue n x =
      milnorKTheoryMap (residueFieldAtOriginEquiv k).symm.toRingHom n
        (dvrMilnorTameSymbol' (localRingAtOrigin k) (RatFunc k) n
          (milnorKTheoryMap
            (AlgebraicGeometry.projectiveLineChartInversion k).toRingHom (n + 1) x)) := by
  simp only [milnorKTheoryMap_eq_transport]
  rw [dvrMilnorTameSymbol'_eq_of_ramified_identity
    (irreducible_algebraMap_X (k := k))]
  rfl

private theorem dvrMilnorTameSymbol'_map_identification
    {R S F E A : Type u}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field F] [Field E] [Field A]
    [Algebra R F] [IsFractionRing R F] [Algebra S E] [IsFractionRing S E]
    (j : R →+* S) [IsLocalHom j] (f : F →+* E)
    (hf : ∀ a : R, f (algebraMap R F a) = algebraMap S E (j a))
    (eR : ResidueField R →+* A) (eS : ResidueField S →+* A)
    (he : eS.comp (ResidueField.map j) = eR)
    {π : R} (hπ : Irreducible π) (hjπ : Irreducible (j π))
    (n : ℕ) (x : MilnorKTheory F (n + 1)) :
    milnorKTheoryMap eS n
        (dvrMilnorTameSymbol' S E n (milnorKTheoryMap f (n + 1) x)) =
      milnorKTheoryMap eR n (dvrMilnorTameSymbol' R F n x) := by
  have h := DFunLike.congr_fun
    (dvrMilnorTameSymbol'_map_ramified (R := R) (S := S) (F := F) (E := E)
      j f hf hπ hjπ (1 : Sˣ) 1 (by simp) n) x
  simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
    Nat.cast_one, one_smul] at h
  rw [h]
  change ((milnorKTheoryMap eS n).comp (milnorKTheoryMap (ResidueField.map j) n))
    (dvrMilnorTameSymbol' R F n x) = _
  rw [← milnorKTheoryMap_comp, he]

variable {d : ℕ}


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

local instance rationalPureOrigin_finiteRatFunc
    (p : MonicIrreducibleOfDegree k d) :
    Module.Finite (RatFunc k) (RatFunc (AdjoinRoot (poly p))) :=
  FiniteDimensional.of_finrank_pos (by
    rw [AdjoinRoot.finrank_ratFunc_adjoinRoot]
    exact (irreducible p).natDegree_pos)

private theorem dvrMilnorTameSymbol'_originToPowerSeries
    (p : MonicIrreducibleOfDegree k d) (n : ℕ)
    (x : MilnorKTheory (RatFunc (AdjoinRoot (poly p))) (n + 1)) :
    milnorKTheoryMap (AdjoinRoot.powerSeriesResidueEquiv (poly p)).toRingHom n
        (dvrMilnorTameSymbol'
          (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))
          (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) n
          (milnorKTheoryMap (ratFuncToLaurentRoot p) (n + 1) x)) =
      milnorKTheoryMap (residueFieldAtOriginEquiv (AdjoinRoot (poly p))).symm.toRingHom n
        (dvrMilnorTameSymbol' (localRingAtOrigin (AdjoinRoot (poly p)))
          (RatFunc (AdjoinRoot (poly p))) n x) := by
  exact dvrMilnorTameSymbol'_map_identification
    (AdjoinRoot.originToPowerSeries (poly p)) (ratFuncToLaurentRoot p)
    (fun a => RingHom.congr_fun (AdjoinRoot.originToPowerSeries_generic_square (poly p)) a)
    (residueFieldAtOriginEquiv (AdjoinRoot (poly p))).symm.toRingHom
    (AdjoinRoot.powerSeriesResidueEquiv (poly p)).toRingHom
    (AdjoinRoot.powerSeriesResidueEquiv_comp_residueField_map_originToPowerSeries (poly p))
    (irreducible_algebraMap_X (k := AdjoinRoot (poly p)))
    (AdjoinRoot.irreducible_originToPowerSeries_X (poly p)) n x

variable (p : MonicIrreducibleOfDegree k d) [IsPurelyInseparable k (AdjoinRoot (poly p))]

/-- The original rational chosen norm commutes with the actual origin residue,
returned to the original constant fields, for a purely inseparable prime-degree root field. -/
theorem dvrMilnorTameSymbol'_milnorKNorm_ratFunc_origin_of_isPurelyInseparable
    (hp : d.Prime) (n : ℕ) (x : MilnorKTheory (RatFunc (AdjoinRoot (poly p))) (n + 1)) :
    milnorKTheoryMap (residueFieldAtOriginEquiv k).symm.toRingHom n
        (dvrMilnorTameSymbol' (localRingAtOrigin k) (RatFunc k) n
          (milnorKNorm (RatFunc k) (RatFunc (AdjoinRoot (poly p))) (n + 1) x)) =
      milnorKNorm k (AdjoinRoot (poly p)) n
        (milnorKTheoryMap (residueFieldAtOriginEquiv (AdjoinRoot (poly p))).symm.toRingHom n
          (dvrMilnorTameSymbol' (localRingAtOrigin (AdjoinRoot (poly p)))
            (RatFunc (AdjoinRoot (poly p))) n x)) := by
  let f := ratFuncToLaurentRoot p
  have hnorm := milnorKNorm_ratFunc_map_laurentSeries_of_isPurelyInseparable p hp (n + 1) x
  calc
    _ = milnorKTheoryMap PowerSeries.residueFieldOfPowerSeries.toRingHom n
        (dvrMilnorTameSymbol' (PowerSeries k) (LaurentSeries k) n
          (milnorKTheoryMap (algebraMap (RatFunc k) (LaurentSeries k)) (n + 1)
            (milnorKNorm (RatFunc k) (RatFunc (AdjoinRoot (poly p))) (n + 1) x))) :=
      (dvrMilnorTameSymbol'_ratFunc_map_laurentSeries n _).symm
    _ = milnorKTheoryMap PowerSeries.residueFieldOfPowerSeries.toRingHom n
        (dvrMilnorTameSymbol' (PowerSeries k) (LaurentSeries k) n
          (milnorKNorm (LaurentSeries k)
            (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) (n + 1)
            (milnorKTheoryMap f (n + 1) x))) :=
      congrArg (fun y => milnorKTheoryMap PowerSeries.residueFieldOfPowerSeries.toRingHom n
        (dvrMilnorTameSymbol' (PowerSeries k) (LaurentSeries k) n y)) hnorm
    _ = milnorKNorm k (AdjoinRoot (poly p)) n
        (milnorKTheoryMap (AdjoinRoot.powerSeriesResidueEquiv (poly p)).toRingHom n
          (dvrMilnorTameSymbol'
            (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))
            (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) n
            (milnorKTheoryMap f (n + 1) x))) :=
      dvrMilnorTameSymbol'_milnorKNorm_laurentSeries_to_constants_of_isPurelyInseparable p hp n _
    _ = _ := congrArg (milnorKNorm k (AdjoinRoot (poly p)) n)
      (dvrMilnorTameSymbol'_originToPowerSeries p n x)

/-- The original native infinity residue commutes with the original rational
chosen norm, in every degree, for a purely inseparable prime-degree root field. -/
theorem infinityResidue_milnorKNorm_ratFunc_of_isPurelyInseparable (hp : d.Prime) (n : ℕ)
    (x : MilnorKTheory (RatFunc (AdjoinRoot (poly p))) (n + 1)) :
    infinityResidue n
        (milnorKNorm (RatFunc k) (RatFunc (AdjoinRoot (poly p))) (n + 1) x) =
      milnorKNorm k (AdjoinRoot (poly p)) n (infinityResidue n x) := by
  rw [infinityResidue_eq_origin_chartInversion,
    infinityResidue_eq_origin_chartInversion]
  rw [← milnorKNorm_ratFunc_map_chartInversion_of_isPurelyInseparable p hp (n + 1) x]
  exact dvrMilnorTameSymbol'_milnorKNorm_ratFunc_origin_of_isPurelyInseparable p hp n
    (milnorKTheoryMap
      (AlgebraicGeometry.projectiveLineChartInversion (AdjoinRoot (poly p))).toRingHom
      (n + 1) x)

end Stacks.Chow

end
