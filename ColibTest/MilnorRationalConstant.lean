module

import Colib.RingTheory.KTheory.MilnorK.Norm.RationalConstant

open Polynomial Stacks.Chow MonicIrreducibleOfDegree
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

-- The left-hand side is the existing chosen native norm, not a second norm
-- defined by transporting a polynomial presentation.
example (hp : d.Prime) (x : MilnorKRing (RatFunc (AdjoinRoot (poly p)))) :
    milnorKNormRing (RatFunc k) (RatFunc (AdjoinRoot (poly p))) x =
      simpleMilnorNorm p.ratFunc
        (milnorKRingMap
          (AdjoinRoot.rationalCoefficientAlgEquiv (poly p) (monic p)).symm.toRingHom x) :=
  milnorKNormRing_ratFunc_eq_simpleMilnorNorm p hp x

example (hp : d.Prime) (x : MilnorKRing (AdjoinRoot (poly p))) :
    milnorKNormRing (RatFunc k) (RatFunc (AdjoinRoot (poly p)))
        (milnorKRingMap (RatFunc.C : AdjoinRoot (poly p) →+*
          RatFunc (AdjoinRoot (poly p))) x) =
      milnorKRingMap (RatFunc.C : k →+* RatFunc k)
        (milnorKNormRing k (AdjoinRoot (poly p)) x) :=
  milnorKNormRing_ratFunc_map_C p hp x
