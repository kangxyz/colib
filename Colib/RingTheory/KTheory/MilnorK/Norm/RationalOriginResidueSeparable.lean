/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.AdjoinRoot.OriginGenericSquare
public import Colib.RingTheory.KTheory.MilnorK.Norm.LaurentPrimeSeparable
public import Colib.RingTheory.KTheory.MilnorK.Norm.RationalCompletionSeparable
public import Colib.RingTheory.KTheory.MilnorK.Norm.RationalChartSeparable
public import Colib.RingTheory.KTheory.MilnorK.Residue.CanonicalRamifiedMap
public import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.InfinityResidue

/-!
# The original rational norm commutes with the origin and infinity residues

For an original monic separable normal prime-degree root field over an arbitrary base,
the original chosen norm on rational functions commutes with the native origin
residue, in every homogeneous degree. The proof descends the actual Laurent
norm-residue square through the original origin local rings. The two generic
squares and the two residue-field dictionaries are proved for their actual maps.
No compatibility square is an additional hypothesis.

The infinity statement uses the original projective-line chart inversion and
the original native infinity residue. No norm, local ring, residue field,
completion field or scalar action is replaced. General finite-place branch sums,
prime diamonds and chosen-norm tower laws are not asserted here.
-/

@[expose] public noncomputable section

open Polynomial IsLocalRing Module
open scoped RatFunc
attribute [local instance] Polynomial.algebra

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree
attribute [local instance] Ideal.Quotient.field

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

local instance (p : MonicIrreducibleOfDegree k d) : Fact (poly p).Monic :=
  ⟨monic p⟩

local instance (p : MonicIrreducibleOfDegree k d) : Fact (Irreducible (poly p)) :=
  ⟨irreducible p⟩

local instance (p : MonicIrreducibleOfDegree k d) :
    Fact (Irreducible ((poly p).map (algebraMap k (LaurentSeries k)))) :=
  ⟨(monic p).irreducible_map_laurentSeries_C (irreducible p)⟩

local instance (p : MonicIrreducibleOfDegree k d) :
    IsDomain (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k))) :=
  AdjoinRoot.isDomain_of_irreducible_map_residue ((monic p).map _)
    ((monic p).irreducible_map_powerSeries_C_residue (irreducible p))

local instance (p : MonicIrreducibleOfDegree k d) :
    IsLocalRing (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k))) :=
  AdjoinRoot.isLocalRing_of_irreducible_map_residue ((monic p).map _)
    ((monic p).irreducible_map_powerSeries_C_residue (irreducible p))

local instance (p : MonicIrreducibleOfDegree k d) :
    IsDiscreteValuationRing
      (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k))) := by
  apply AdjoinRoot.isDiscreteValuationRing ((monic p).map _)
    ((monic p).irreducible_map_powerSeries_C_residue (irreducible p))
  rw [(monic p).natDegree_map]
  exact (irreducible p).natDegree_pos

local instance (p : MonicIrreducibleOfDegree k d) :
    Module.Finite (PowerSeries k)
      (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k))) :=
  ((monic p).map _).finite_adjoinRoot

local instance (p : MonicIrreducibleOfDegree k d) :
    Module.IsTorsionFree (PowerSeries k)
      (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k))) := by
  apply AdjoinRoot.isTorsionFree_of_prime_of_degree_ne_zero
    (AdjoinRoot.prime_of_irreducible_map_residue ((monic p).map _)
      ((monic p).irreducible_map_powerSeries_C_residue (irreducible p)))
  apply ne_of_gt
  apply natDegree_pos_iff_degree_pos.mp
  rw [(monic p).natDegree_map]
  exact (irreducible p).natDegree_pos

local instance (p : MonicIrreducibleOfDegree k d) : IsLocalHom
    (algebraMap (PowerSeries k)
      (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))) := by
  rw [AdjoinRoot.algebraMap_eq]
  exact AdjoinRoot.isLocalHom_of_monic ((monic p).map _)

local instance (p : MonicIrreducibleOfDegree k d) :
    Algebra (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))
      (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) :=
  (Stacks.AdjoinRootFraction.toMapAdjoinRoot (LaurentSeries k)
    (p := (poly p).map (PowerSeries.C : k →+* PowerSeries k))
    (q := (poly p).map (algebraMap k (LaurentSeries k)))
    (by rw [Polynomial.map_map]; rfl)).toAlgebra

local instance (p : MonicIrreducibleOfDegree k d) :
    IsScalarTower (PowerSeries k)
      (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))
      (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) := by
  apply IsScalarTower.of_algebraMap_eq
  intro a
  exact (Stacks.AdjoinRootFraction.toMapAdjoinRoot_of (LaurentSeries k)
    (p := (poly p).map (PowerSeries.C : k →+* PowerSeries k))
    (q := (poly p).map (algebraMap k (LaurentSeries k)))
    (by rw [Polynomial.map_map]; rfl) a).symm

local instance (p : MonicIrreducibleOfDegree k d) :
    IsFractionRing
      (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))
      (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) :=
  Stacks.AdjoinRootFraction.isFractionRing_adjoinRoot (LaurentSeries k)
    (p := (poly p).map (PowerSeries.C : k →+* PowerSeries k))
    (q := (poly p).map (algebraMap k (LaurentSeries k)))
    (by rw [Polynomial.map_map]; rfl) (RingEquiv.refl _) ((monic p).map _)
    (by ext <;> rfl)

local instance (p : MonicIrreducibleOfDegree k d) :
    Module.Finite k (AdjoinRoot (poly p)) := (monic p).finite_adjoinRoot

local instance (p : MonicIrreducibleOfDegree k d) :
    Module.Finite (LaurentSeries k)
      (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) :=
  ((monic p).map _).finite_adjoinRoot

local instance (p : MonicIrreducibleOfDegree k d) :
    Module.Finite (RatFunc k) (RatFunc (AdjoinRoot (poly p))) :=
  FiniteDimensional.of_finrank_pos (by
    rw [AdjoinRoot.finrank_ratFunc_adjoinRoot]
    exact (irreducible p).natDegree_pos)

local instance rationalOriginResidue_factIrreducibleRatFuncSeparable
    (p : MonicIrreducibleOfDegree k d) :
    Fact (Irreducible ((poly p).map (RatFunc.C : k →+* RatFunc k))) :=
  ⟨(monic p).irreducible_map_ratFunc_C (irreducible p)⟩

private theorem originToPowerSeries_generic_square_apply
    (p : MonicIrreducibleOfDegree k d) (a : localRingAtOrigin (AdjoinRoot (poly p))) :
    (RingHom.comp
      (AdjoinRoot.map (algebraMap (RatFunc k) (LaurentSeries k))
        ((poly p).map (RatFunc.C : k →+* RatFunc k))
        ((poly p).map (algebraMap k (LaurentSeries k))) (by
          rw [Polynomial.map_map, RatFunc.algebraMap_laurentSeries_comp_C]))
      (AdjoinRoot.rationalCoefficientAlgEquiv (poly p) (monic p)).symm.toRingHom)
        (algebraMap (localRingAtOrigin (AdjoinRoot (poly p)))
          (RatFunc (AdjoinRoot (poly p))) a) =
      algebraMap (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))
        (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k))))
        (AdjoinRoot.originToPowerSeries (poly p) a) :=
  RingHom.congr_fun (AdjoinRoot.originToPowerSeries_generic_square (poly p)) a

private theorem dvrMilnorTameSymbol'_originToPowerSeries
    (p : MonicIrreducibleOfDegree k d) (n : ℕ)
    (x : MilnorKTheory (RatFunc (AdjoinRoot (poly p))) (n + 1)) :
    milnorKTheoryMap (AdjoinRoot.powerSeriesResidueEquiv (poly p)).toRingHom n
        (dvrMilnorTameSymbol'
          (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))
          (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) n
          (milnorKTheoryMap
            (RingHom.comp
              (AdjoinRoot.map (algebraMap (RatFunc k) (LaurentSeries k))
                ((poly p).map (RatFunc.C : k →+* RatFunc k))
                ((poly p).map (algebraMap k (LaurentSeries k))) (by
                  rw [Polynomial.map_map, RatFunc.algebraMap_laurentSeries_comp_C]))
              (AdjoinRoot.rationalCoefficientAlgEquiv (poly p) (monic p)).symm.toRingHom)
            (n + 1) x)) =
      milnorKTheoryMap (residueFieldAtOriginEquiv (AdjoinRoot (poly p))).symm.toRingHom n
        (dvrMilnorTameSymbol' (localRingAtOrigin (AdjoinRoot (poly p)))
          (RatFunc (AdjoinRoot (poly p))) n x) := by
  exact dvrMilnorTameSymbol'_map_identification
    (R := localRingAtOrigin (AdjoinRoot (poly p)))
    (S := AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))
    (F := RatFunc (AdjoinRoot (poly p)))
    (E := AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k))))
    (A := AdjoinRoot (poly p))
    (AdjoinRoot.originToPowerSeries (poly p))
    (RingHom.comp
      (AdjoinRoot.map (algebraMap (RatFunc k) (LaurentSeries k))
        ((poly p).map (RatFunc.C : k →+* RatFunc k))
        ((poly p).map (algebraMap k (LaurentSeries k))) (by
          rw [Polynomial.map_map, RatFunc.algebraMap_laurentSeries_comp_C]))
      (AdjoinRoot.rationalCoefficientAlgEquiv (poly p) (monic p)).symm.toRingHom)
    (originToPowerSeries_generic_square_apply p)
    (residueFieldAtOriginEquiv (AdjoinRoot (poly p))).symm.toRingHom
    (AdjoinRoot.powerSeriesResidueEquiv (poly p)).toRingHom
    (AdjoinRoot.powerSeriesResidueEquiv_comp_residueField_map_originToPowerSeries (poly p))
    (irreducible_algebraMap_X (k := AdjoinRoot (poly p)))
    (AdjoinRoot.irreducible_originToPowerSeries_X (poly p)) n x

variable (p : MonicIrreducibleOfDegree k d) (hsep : (poly p).Separable)
  [Normal k (AdjoinRoot (poly p))]

include hsep

/-- The original rational chosen norm restricts to the literal Laurent root field
in every homogeneous degree, with the original coefficient/root map. -/
theorem milnorKNorm_ratFunc_map_laurentSeries_of_separable (hp : d.Prime) (n : ℕ)
    (x : MilnorKTheory (RatFunc (AdjoinRoot (poly p))) n) :
    milnorKTheoryMap (algebraMap (RatFunc k) (LaurentSeries k)) n
        (milnorKNorm (RatFunc k) (RatFunc (AdjoinRoot (poly p))) n x) =
      milnorKNorm (LaurentSeries k)
        (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) n
        (milnorKTheoryMap
          (RingHom.comp
            (AdjoinRoot.map (algebraMap (RatFunc k) (LaurentSeries k))
              ((poly p).map (RatFunc.C : k →+* RatFunc k))
              ((poly p).map (algebraMap k (LaurentSeries k))) (by
                rw [Polynomial.map_map, RatFunc.algebraMap_laurentSeries_comp_C]))
            (AdjoinRoot.rationalCoefficientAlgEquiv (poly p) (monic p)).symm.toRingHom)
          n x) := by
  simp only [milnorKTheoryMap_eq_transport]
  apply Subtype.ext
  exact milnorKNormRing_ratFunc_map_laurentSeries_of_separable p hsep hp (x : MilnorKRing _)

/-- The original rational chosen norm commutes with the actual origin residue,
returned to the original constant fields, for a normal prime-degree root field. -/
theorem dvrMilnorTameSymbol'_milnorKNorm_ratFunc_origin_of_separable (hp : d.Prime) (n : ℕ)
    (x : MilnorKTheory (RatFunc (AdjoinRoot (poly p))) (n + 1)) :
    milnorKTheoryMap (residueFieldAtOriginEquiv k).symm.toRingHom n
        (dvrMilnorTameSymbol' (localRingAtOrigin k) (RatFunc k) n
          (milnorKNorm (RatFunc k) (RatFunc (AdjoinRoot (poly p))) (n + 1) x)) =
      milnorKNorm k (AdjoinRoot (poly p)) n
        (milnorKTheoryMap (residueFieldAtOriginEquiv (AdjoinRoot (poly p))).symm.toRingHom n
          (dvrMilnorTameSymbol' (localRingAtOrigin (AdjoinRoot (poly p)))
            (RatFunc (AdjoinRoot (poly p))) n x)) := by
  let f : RatFunc (AdjoinRoot (poly p)) →+*
      AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k))) := RingHom.comp
    (AdjoinRoot.map (algebraMap (RatFunc k) (LaurentSeries k))
      ((poly p).map (RatFunc.C : k →+* RatFunc k))
      ((poly p).map (algebraMap k (LaurentSeries k))) (by
        rw [Polynomial.map_map, RatFunc.algebraMap_laurentSeries_comp_C]))
    (AdjoinRoot.rationalCoefficientAlgEquiv (poly p) (monic p)).symm.toRingHom
  have hnorm : milnorKTheoryMap (algebraMap (RatFunc k) (LaurentSeries k)) (n + 1)
      (milnorKNorm (RatFunc k) (RatFunc (AdjoinRoot (poly p))) (n + 1) x) =
    milnorKNorm (LaurentSeries k)
      (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) (n + 1)
      (milnorKTheoryMap f (n + 1) x) :=
    milnorKNorm_ratFunc_map_laurentSeries_of_separable p hsep hp (n + 1) x
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
      dvrMilnorTameSymbol'_milnorKNorm_laurentSeries_to_constants_of_separable p hsep hp n _
    _ = _ := congrArg (milnorKNorm k (AdjoinRoot (poly p)) n)
      (dvrMilnorTameSymbol'_originToPowerSeries p n x)

/-- The original rational chosen norm commutes with native chart inversion in
every homogeneous degree. -/
theorem milnorKNorm_ratFunc_map_chartInversion_of_separable (hp : d.Prime) (n : ℕ)
    (x : MilnorKTheory (RatFunc (AdjoinRoot (poly p))) n) :
    milnorKNorm (RatFunc k) (RatFunc (AdjoinRoot (poly p))) n
        (milnorKTheoryMap
          (AlgebraicGeometry.projectiveLineChartInversion (AdjoinRoot (poly p))).toRingHom n x) =
      milnorKTheoryMap (AlgebraicGeometry.projectiveLineChartInversion k).toRingHom n
        (milnorKNorm (RatFunc k) (RatFunc (AdjoinRoot (poly p))) n x) := by
  simp only [milnorKTheoryMap_eq_transport]
  apply Subtype.ext
  exact milnorKNormRing_ratFunc_map_chartInversion_of_separable p hsep hp (x : MilnorKRing _)

/-- The original native infinity residue commutes with the original rational
chosen norm, in every degree, for a normal prime-degree root field. -/
theorem infinityResidue_milnorKNorm_ratFunc_of_separable (hp : d.Prime) (n : ℕ)
    (x : MilnorKTheory (RatFunc (AdjoinRoot (poly p))) (n + 1)) :
    infinityResidue n
        (milnorKNorm (RatFunc k) (RatFunc (AdjoinRoot (poly p))) (n + 1) x) =
      milnorKNorm k (AdjoinRoot (poly p)) n (infinityResidue n x) := by
  rw [infinityResidue_eq_origin_chartInversion,
    infinityResidue_eq_origin_chartInversion]
  rw [← milnorKNorm_ratFunc_map_chartInversion_of_separable p hsep hp (n + 1) x]
  exact dvrMilnorTameSymbol'_milnorKNorm_ratFunc_origin_of_separable p hsep hp n
    (milnorKTheoryMap
      (AlgebraicGeometry.projectiveLineChartInversion (AdjoinRoot (poly p))).toRingHom
      (n + 1) x)

end Stacks.Chow
