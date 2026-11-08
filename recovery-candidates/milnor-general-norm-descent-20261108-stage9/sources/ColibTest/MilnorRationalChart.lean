module

import Colib.RingTheory.KTheory.MilnorK.Norm.RationalChart

open Polynomial AlgebraicGeometry Stacks.Chow MonicIrreducibleOfDegree
open scoped RatFunc
attribute [local instance] Polynomial.algebra Ideal.Quotient.field

universe u

variable {k : Type u} [Field k] [CharZero k] {d : ℕ}
  (p : MonicIrreducibleOfDegree k d)

local instance : Fact (Irreducible (poly p)) := ⟨irreducible p⟩

local instance : Module.Finite k (AdjoinRoot (poly p)) :=
  (AdjoinRoot.powerBasis (ne_zero p)).finite

local instance : Module.Finite (RatFunc k) (RatFunc (AdjoinRoot (poly p))) :=
  FiniteDimensional.of_finrank_pos (by
    rw [AdjoinRoot.finrank_ratFunc_adjoinRoot]
    exact (irreducible p).natDegree_pos)

variable [Normal k (AdjoinRoot (poly p))]

example (hp : d.Prime) (x : MilnorKRing (RatFunc (AdjoinRoot (poly p)))) :
    milnorKNormRing (RatFunc k) (RatFunc (AdjoinRoot (poly p)))
        (milnorKRingMap (projectiveLineChartInversion (AdjoinRoot (poly p))).toRingHom x) =
      milnorKRingMap (projectiveLineChartInversion k).toRingHom
        (milnorKNormRing (RatFunc k) (RatFunc (AdjoinRoot (poly p))) x) :=
  milnorKNormRing_ratFunc_map_chartInversion p hp x
