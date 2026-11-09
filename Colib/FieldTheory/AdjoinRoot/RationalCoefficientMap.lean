/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.FieldTheory.AdjoinRoot.RationalCoefficient
public import Colib.FieldTheory.AdjoinRoot.NormalScalar

/-!
# Naturality of the actual rational coefficient root comparison

The coefficient map and both root maps below are Mathlib's original maps. The
comparison is the original `AdjoinRoot.rationalCoefficientAlgEquiv`. In particular,
the naturality square is proved on the base rational functions and the actual
adjoined root; it is not an additional hypothesis or a transported field model.
-/

@[expose] public noncomputable section

open Polynomial
open scoped RatFunc nonZeroDivisors
attribute [local instance] Polynomial.algebra

universe u v

variable {k : Type u} [Field k] {K : Type v} [Field K]

namespace RatFunc

/-- The native rational coefficient map takes constants to the supplied constants. -/
theorem mapRingHom_coefficient_C (φ : k →+* K) (a : k) :
    RatFunc.mapRingHom (Polynomial.mapRingHom φ)
      (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ) (RatFunc.C a) =
        RatFunc.C (φ a) := by
  rw [← RatFunc.algebraMap_C, RatFunc.mapRingHom_algebraMap]
  change algebraMap K[X] (RatFunc K) ((Polynomial.C a).map φ) = _
  rw [Polynomial.map_C, RatFunc.algebraMap_C]

end RatFunc

namespace Polynomial

/-- Rationalizing and then changing coefficients is the same actual polynomial
as changing coefficients and then rationalizing. -/
theorem map_ratFunc_C_mapRingHom (φ : k →+* K) (p : k[X]) :
    (p.map (RatFunc.C : k →+* RatFunc k)).map
        (RatFunc.mapRingHom (Polynomial.mapRingHom φ)
          (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)) =
      (p.map φ).map (RatFunc.C : K →+* RatFunc K) := by
  have hcoeff :
      (RatFunc.mapRingHom (Polynomial.mapRingHom φ)
        (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)).comp
          (RatFunc.C : k →+* RatFunc k) =
        (RatFunc.C : K →+* RatFunc K).comp φ := by
    apply RingHom.ext
    intro a
    exact RatFunc.mapRingHom_coefficient_C φ a
  rw [Polynomial.map_map, Polynomial.map_map, hcoeff]

/-- Divisibility in the actual mapped coefficient polynomial rationalizes to the
exact divisibility required by the native rational root map. -/
theorem dvd_map_ratFunc_C_mapRingHom (φ : k →+* K) (p : k[X]) (q : K[X])
    (hq : q ∣ p.map φ) :
    q.map (RatFunc.C : K →+* RatFunc K) ∣
      (p.map (RatFunc.C : k →+* RatFunc k)).map
        (RatFunc.mapRingHom (Polynomial.mapRingHom φ)
          (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)) := by
  rw [map_ratFunc_C_mapRingHom]
  exact Polynomial.map_dvd (RatFunc.C : K →+* RatFunc K) hq

end Polynomial

namespace AdjoinRoot

/-- Normality of the original root field persists for its actual rational
function field. This uses the literal rationalized splitting field and the
original rational coefficient comparison. -/
theorem normal_ratFunc_adjoinRoot (p : k[X]) [Fact (Irreducible p)]
    (hp : p.Monic) [Normal k (AdjoinRoot p)] :
    Normal (RatFunc k) (RatFunc (AdjoinRoot p)) := by
  let rationalCoefficientMapIrreducible :
      Fact (Irreducible (p.map (RatFunc.C : k →+* RatFunc k))) :=
    ⟨hp.irreducible_map_ratFunc_C Fact.out⟩
  let rationalCoefficientMapSplitting :
      IsSplittingField (RatFunc k)
        (AdjoinRoot (p.map (RatFunc.C : k →+* RatFunc k)))
        (p.map (RatFunc.C : k →+* RatFunc k)) :=
    AdjoinRoot.isSplittingField_of_dvd_map hp dvd_rfl
  let rationalCoefficientMapNormal : Normal (RatFunc k)
      (AdjoinRoot (p.map (RatFunc.C : k →+* RatFunc k))) :=
    Normal.of_isSplittingField (p.map (RatFunc.C : k →+* RatFunc k))
  exact Normal.of_algEquiv (rationalCoefficientAlgEquiv p hp)

variable (φ : k →+* K) (p : k[X]) (q : K[X])
  [Fact (Irreducible p)] [Fact (Irreducible q)]

/-- The actual rational coefficient comparison commutes with the original root
map for any irreducible factor of the changed coefficient polynomial. -/
theorem rationalCoefficientAlgEquiv_mapRingHom
    (hp : p.Monic) (hqmonic : q.Monic) (hq : q ∣ p.map φ) :
    let rationalMap := RatFunc.mapRingHom (Polynomial.mapRingHom φ)
      (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)
    let rootMap := AdjoinRoot.map φ p q hq
    let rationalMapOfRoot := RatFunc.mapRingHom (Polynomial.mapRingHom rootMap)
      (Polynomial.nonZeroDivisors_le_comap_mapRingHom rootMap)
    let rootMapOverRat := AdjoinRoot.map rationalMap
      (p.map (RatFunc.C : k →+* RatFunc k))
      (q.map (RatFunc.C : K →+* RatFunc K))
      (Polynomial.dvd_map_ratFunc_C_mapRingHom φ p q hq)
    (rationalCoefficientAlgEquiv q hqmonic).toRingHom.comp rootMapOverRat =
      rationalMapOfRoot.comp (rationalCoefficientAlgEquiv p hp).toRingHom := by
  let rationalMap := RatFunc.mapRingHom (Polynomial.mapRingHom φ)
    (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)
  let rootMap := AdjoinRoot.map φ p q hq
  let rationalMapOfRoot := RatFunc.mapRingHom (Polynomial.mapRingHom rootMap)
    (Polynomial.nonZeroDivisors_le_comap_mapRingHom rootMap)
  let rootMapOverRat := AdjoinRoot.map rationalMap
    (p.map (RatFunc.C : k →+* RatFunc k))
    (q.map (RatFunc.C : K →+* RatFunc K))
    (Polynomial.dvd_map_ratFunc_C_mapRingHom φ p q hq)
  change (rationalCoefficientAlgEquiv q hqmonic).toRingHom.comp rootMapOverRat =
    rationalMapOfRoot.comp (rationalCoefficientAlgEquiv p hp).toRingHom
  have hcoeff : rootMap.comp (algebraMap k (AdjoinRoot p)) =
      (algebraMap K (AdjoinRoot q)).comp φ := by
    apply RingHom.ext
    intro a
    exact AdjoinRoot.map_of φ p q hq a
  have hbase : rationalMapOfRoot.comp
      (algebraMap (RatFunc k) (RatFunc (AdjoinRoot p))) =
      (algebraMap (RatFunc K) (RatFunc (AdjoinRoot q))).comp rationalMap := by
    rw [RatFunc.algebraMap_eq_mapRingHom, RatFunc.algebraMap_eq_mapRingHom]
    apply IsLocalization.ringHom_ext (nonZeroDivisors k[X])
    apply RingHom.ext
    intro a
    change rationalMapOfRoot
        (RatFunc.mapRingHom (Polynomial.mapRingHom (algebraMap k (AdjoinRoot p)))
          (Polynomial.nonZeroDivisors_le_comap_mapRingHom
            (algebraMap k (AdjoinRoot p))) (algebraMap k[X] (RatFunc k) a)) =
      RatFunc.mapRingHom (Polynomial.mapRingHom (algebraMap K (AdjoinRoot q)))
        (Polynomial.nonZeroDivisors_le_comap_mapRingHom
          (algebraMap K (AdjoinRoot q)))
        (rationalMap (algebraMap k[X] (RatFunc k) a))
    dsimp only [rationalMapOfRoot, rationalMap]
    simp only [RatFunc.mapRingHom_algebraMap]
    congr 1
    change (a.map (algebraMap k (AdjoinRoot p))).map rootMap =
      (a.map φ).map (algebraMap K (AdjoinRoot q))
    rw [Polynomial.map_map, Polynomial.map_map, hcoeff]
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext
    intro a
    change rationalCoefficientAlgEquiv q hqmonic
        (rootMapOverRat (AdjoinRoot.of (p.map RatFunc.C) a)) =
      rationalMapOfRoot
        (rationalCoefficientAlgEquiv p hp (AdjoinRoot.of (p.map RatFunc.C) a))
    dsimp only [rootMapOverRat]
    rw [AdjoinRoot.map_of]
    change rationalCoefficientAlgEquiv q hqmonic
        (algebraMap (RatFunc K) (AdjoinRoot (q.map RatFunc.C)) (rationalMap a)) =
      rationalMapOfRoot (rationalCoefficientAlgEquiv p hp
        (algebraMap (RatFunc k) (AdjoinRoot (p.map RatFunc.C)) a))
    rw [AlgEquiv.commutes, AlgEquiv.commutes]
    exact (RingHom.congr_fun hbase a).symm
  · change rationalCoefficientAlgEquiv q hqmonic
        (rootMapOverRat (AdjoinRoot.root (p.map RatFunc.C))) =
      rationalMapOfRoot
        (rationalCoefficientAlgEquiv p hp (AdjoinRoot.root (p.map RatFunc.C)))
    dsimp only [rootMapOverRat, rationalMapOfRoot]
    rw [AdjoinRoot.map_root, rationalCoefficientAlgEquiv_root,
      rationalCoefficientAlgEquiv_root, RatFunc.mapRingHom_coefficient_C]
    exact congrArg RatFunc.C (AdjoinRoot.map_root φ p q hq).symm

/-- The inverse orientation of the actual coefficient-root square, ready for
transport of norms across the original branch equivalences. -/
theorem rationalCoefficientAlgEquiv_symm_mapRingHom
    (hp : p.Monic) (hqmonic : q.Monic) (hq : q ∣ p.map φ) :
    let rationalMap := RatFunc.mapRingHom (Polynomial.mapRingHom φ)
      (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)
    let rootMap := AdjoinRoot.map φ p q hq
    let rationalMapOfRoot := RatFunc.mapRingHom (Polynomial.mapRingHom rootMap)
      (Polynomial.nonZeroDivisors_le_comap_mapRingHom rootMap)
    let rootMapOverRat := AdjoinRoot.map rationalMap
      (p.map (RatFunc.C : k →+* RatFunc k))
      (q.map (RatFunc.C : K →+* RatFunc K))
      (Polynomial.dvd_map_ratFunc_C_mapRingHom φ p q hq)
    (rationalCoefficientAlgEquiv q hqmonic).symm.toRingHom.comp rationalMapOfRoot =
      rootMapOverRat.comp (rationalCoefficientAlgEquiv p hp).symm.toRingHom := by
  dsimp only
  apply RingHom.ext
  intro x
  apply (rationalCoefficientAlgEquiv q hqmonic).injective
  change rationalCoefficientAlgEquiv q hqmonic
      ((rationalCoefficientAlgEquiv q hqmonic).symm _) = _
  rw [AlgEquiv.apply_symm_apply]
  have h := RingHom.congr_fun
    (rationalCoefficientAlgEquiv_mapRingHom φ p q hp hqmonic hq)
    ((rationalCoefficientAlgEquiv p hp).symm x)
  change rationalCoefficientAlgEquiv q hqmonic _ =
    RatFunc.mapRingHom (Polynomial.mapRingHom (AdjoinRoot.map φ p q hq))
      (Polynomial.nonZeroDivisors_le_comap_mapRingHom (AdjoinRoot.map φ p q hq))
      (rationalCoefficientAlgEquiv p hp ((rationalCoefficientAlgEquiv p hp).symm x)) at h
  rw [AlgEquiv.apply_symm_apply] at h
  exact h.symm

end AdjoinRoot
