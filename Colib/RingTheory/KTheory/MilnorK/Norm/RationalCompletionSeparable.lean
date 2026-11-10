/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.RationalConstantSeparable
public import Colib.RingTheory.Polynomial.SeriesIrreducible

/-!
# Restricting the original rational chosen norm to the actual Laurent root field

The original chosen norm on RatFunc of the original root field restricts to the
chosen norm of the literal constant-polynomial root field over LaurentSeries.
The upper map is the original AdjoinRoot.map composed with the inverse of the
proved rationalCoefficientAlgEquiv. No rational norm or completion-root map is
redefined. Normality and the prime generic degree are proved for the actual
Laurent root field, and both chosen norms use their proved native presentations.

This is the norm restriction step for the complete linear residue square. It
is not that residue square or a general norm base-change/tower theorem.
-/

@[expose] public noncomputable section

open Polynomial
open scoped RatFunc
attribute [local instance] Polynomial.algebra

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree
attribute [local instance] Ideal.Quotient.field

variable {k : Type u} [Field k] {d : ℕ}

local instance rationalCompletion_instFactIrreducibleSeparable (p : MonicIrreducibleOfDegree k d) :
    Fact (Irreducible (poly p)) :=
  ⟨irreducible p⟩

local instance rationalCompletion_instFactLaurentIrreducibleSeparable
    (p : MonicIrreducibleOfDegree k d) :
    Fact (Irreducible ((poly p).map (algebraMap k (LaurentSeries k)))) :=
  ⟨(monic p).irreducible_map_laurentSeries_C (irreducible p)⟩

local instance rationalCompletion_instFiniteRootSeparable (p : MonicIrreducibleOfDegree k d) :
    Module.Finite k (AdjoinRoot (poly p)) := (monic p).finite_adjoinRoot

local instance rationalCompletion_instFiniteRatFuncRootSeparable
    (p : MonicIrreducibleOfDegree k d) :
    Module.Finite (RatFunc k) (RatFunc (AdjoinRoot (poly p))) :=
  FiniteDimensional.of_finrank_pos (by
    rw [AdjoinRoot.finrank_ratFunc_adjoinRoot]
    exact (irreducible p).natDegree_pos)

local instance rationalCompletion_instFiniteLaurentRootSeparable
    (p : MonicIrreducibleOfDegree k d) :
    Module.Finite (LaurentSeries k)
      (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) :=
  ((monic p).map _).finite_adjoinRoot

variable (p : MonicIrreducibleOfDegree k d) (hsep : (poly p).Separable)
  [Normal k (AdjoinRoot (poly p))]

include hsep

/-- The original rational chosen norm restricts to the actual Laurent root-field
chosen norm, along the literal coefficient/root presentation map. -/
theorem milnorKNormRing_ratFunc_map_laurentSeries_of_separable (hp : d.Prime)
    (x : MilnorKRing (RatFunc (AdjoinRoot (poly p)))) :
    milnorKRingMap (algebraMap (RatFunc k) (LaurentSeries k))
        (milnorKNormRing (RatFunc k) (RatFunc (AdjoinRoot (poly p))) x) =
      milnorKNormRing (LaurentSeries k)
        (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k))))
        (milnorKRingMap
          (RingHom.comp (AdjoinRoot.map (algebraMap (RatFunc k) (LaurentSeries k))
            ((poly p).map (RatFunc.C : k →+* RatFunc k))
            ((poly p).map (algebraMap k (LaurentSeries k))) (by
              change (poly p).map (algebraMap k (LaurentSeries k)) ∣
                ((poly p).map (algebraMap k (RatFunc k))).map
                  (algebraMap (RatFunc k) (LaurentSeries k))
              have hc : (algebraMap (RatFunc k) (LaurentSeries k)).comp
                  (algebraMap k (RatFunc k)) = algebraMap k (LaurentSeries k) := by
                apply RingHom.ext
                intro a
                change algebraMap (RatFunc k) (LaurentSeries k) (RatFunc.C a) =
                  HahnSeries.ofPowerSeries ℤ k (PowerSeries.C a)
                rw [← RatFunc.algebraMap_C,
                  ← IsScalarTower.algebraMap_apply k[X] (RatFunc k) (LaurentSeries k)]
                change HahnSeries.ofPowerSeries ℤ k ((Polynomial.C a : k[X]) : PowerSeries k) =
                  HahnSeries.ofPowerSeries ℤ k (PowerSeries.C a)
                rw [Polynomial.coe_C]
              rw [Polynomial.map_map, hc]))
            (AdjoinRoot.rationalCoefficientAlgEquiv (poly p) (monic p)).symm.toRingHom) x) := by
  let : Fact (Irreducible ((poly p).map (RatFunc.C : k →+* RatFunc k))) :=
    ⟨(monic p).irreducible_map_ratFunc_C (irreducible p)⟩
  let q : MonicIrreducibleOfDegree (LaurentSeries k) d :=
    ⟨(poly p).map (algebraMap k (LaurentSeries k)), (monic p).map _,
      (monic p).irreducible_map_laurentSeries_C (irreducible p),
      (Polynomial.natDegree_map _).trans (natDegree_eq p)⟩
  have hq : poly q = (poly p.ratFunc).map (algebraMap (RatFunc k) (LaurentSeries k)) := by
    change (poly p).map (algebraMap k (LaurentSeries k)) =
      ((poly p).map (algebraMap k (RatFunc k))).map
        (algebraMap (RatFunc k) (LaurentSeries k))
    have hc : (algebraMap (RatFunc k) (LaurentSeries k)).comp
        (algebraMap k (RatFunc k)) = algebraMap k (LaurentSeries k) := by
      apply RingHom.ext
      intro a
      change algebraMap (RatFunc k) (LaurentSeries k) (RatFunc.C a) =
        HahnSeries.ofPowerSeries ℤ k (PowerSeries.C a)
      rw [← RatFunc.algebraMap_C,
        ← IsScalarTower.algebraMap_apply k[X] (RatFunc k) (LaurentSeries k)]
      change HahnSeries.ofPowerSeries ℤ k ((Polynomial.C a : k[X]) : PowerSeries k) =
        HahnSeries.ofPowerSeries ℤ k (PowerSeries.C a)
      rw [Polynomial.coe_C]
    rw [Polynomial.map_map, hc]
  let : IsSplittingField (LaurentSeries k)
      (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k))))
      ((poly p).map (algebraMap k (LaurentSeries k))) :=
    AdjoinRoot.isSplittingField_of_dvd_map (monic p) dvd_rfl
  let : Normal (LaurentSeries k)
      (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) :=
    Normal.of_isSplittingField ((poly p).map (algebraMap k (LaurentSeries k)))
  let : Algebra.IsSeparable (LaurentSeries k)
      (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) :=
    AdjoinRoot.isSeparable_of_polynomial_separable _ hsep.map
  have hprime : Nat.Prime (Module.finrank (LaurentSeries k)
      (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k))))) := by
    rw [(AdjoinRoot.powerBasis
      ((monic p).irreducible_map_laurentSeries_C (irreducible p)).ne_zero).finrank,
      AdjoinRoot.powerBasis_dim, Polynomial.natDegree_map, natDegree_eq]
    exact hp
  let e : AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k))) ≃ₐ[LaurentSeries k]
      ((LaurentSeries k)[X] ⧸ Ideal.span {poly q}) :=
    { toRingEquiv := RingEquiv.refl _
      commutes' := fun _ => rfl }
  have hchosen (y : MilnorKRing
      (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k))))) :
      milnorKNormRing (LaurentSeries k)
        (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) y =
          simpleMilnorNorm q y := by
    calc
      _ = simpleMilnorNorm q (milnorKRingMap e.toRingHom y) :=
        milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_normal_prime_of_separable hprime q e y
      _ = _ := congrArg (simpleMilnorNorm q) (show milnorKRingMap e.toRingHom y = y from
        milnorKRingMap_id_apply y)
  let f := AdjoinRoot.map (algebraMap (RatFunc k) (LaurentSeries k))
    (poly p.ratFunc) (poly q) (hq ▸ dvd_rfl)
  calc
    _ = milnorKRingMap (algebraMap (RatFunc k) (LaurentSeries k))
        (simpleMilnorNorm p.ratFunc
          (milnorKRingMap
            (AdjoinRoot.rationalCoefficientAlgEquiv (poly p) (monic p)).symm.toRingHom x)) :=
      congrArg (milnorKRingMap (algebraMap (RatFunc k) (LaurentSeries k)))
        (milnorKNormRing_ratFunc_eq_simpleMilnorNorm_of_separable p hsep hp x)
    _ = simpleMilnorNorm q (milnorKRingMap f
        (milnorKRingMap
          (AdjoinRoot.rationalCoefficientAlgEquiv (poly p) (monic p)).symm.toRingHom x)) :=
      simpleMilnorNorm_map_of_poly_eq_map (algebraMap (RatFunc k) (LaurentSeries k))
        p.ratFunc q hq _
    _ = simpleMilnorNorm q (milnorKRingMap
        (f.comp (AdjoinRoot.rationalCoefficientAlgEquiv (poly p) (monic p)).symm.toRingHom) x) :=
      congrArg (simpleMilnorNorm q) (milnorKRingMap_comp_apply
        (AdjoinRoot.rationalCoefficientAlgEquiv (poly p) (monic p)).symm.toRingHom f x)
    _ = _ := (hchosen _).symm

end Stacks.Chow
