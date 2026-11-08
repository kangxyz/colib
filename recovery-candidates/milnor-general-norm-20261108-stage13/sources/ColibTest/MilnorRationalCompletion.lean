module

import Colib.RingTheory.KTheory.MilnorK.Norm.RationalCompletion

noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree
open scoped RatFunc
attribute [local instance] Polynomial.algebra Ideal.Quotient.field

universe u

variable {k : Type u} [Field k] {d : ℕ}

local instance (p : MonicIrreducibleOfDegree k d) : Fact (Irreducible (poly p)) :=
  ⟨irreducible p⟩

local instance (p : MonicIrreducibleOfDegree k d) :
    Fact (Irreducible ((poly p).map (algebraMap k (LaurentSeries k)))) :=
  ⟨(monic p).irreducible_map_laurentSeries_C (irreducible p)⟩

local instance (p : MonicIrreducibleOfDegree k d) :
    Module.Finite k (AdjoinRoot (poly p)) := (monic p).finite_adjoinRoot

local instance (p : MonicIrreducibleOfDegree k d) :
    Module.Finite (RatFunc k) (RatFunc (AdjoinRoot (poly p))) :=
  FiniteDimensional.of_finrank_pos (by
    rw [AdjoinRoot.finrank_ratFunc_adjoinRoot]
    exact (irreducible p).natDegree_pos)

local instance (p : MonicIrreducibleOfDegree k d) :
    Module.Finite (LaurentSeries k)
      (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) :=
  ((monic p).map _).finite_adjoinRoot

variable [CharZero k] (p : MonicIrreducibleOfDegree k d)
  [Normal k (AdjoinRoot (poly p))]

local instance : CharZero (LaurentSeries k) :=
  charZero_of_injective_algebraMap (algebraMap k (LaurentSeries k)).injective

example (hp : d.Prime)
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
            (AdjoinRoot.rationalCoefficientAlgEquiv (poly p) (monic p)).symm.toRingHom) x) :=
  milnorKNormRing_ratFunc_map_laurentSeries p hp x
