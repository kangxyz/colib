module

import Colib.RingTheory.KTheory.MilnorK.Norm.RationalTranslation

open Polynomial Stacks.Chow MonicIrreducibleOfDegree
open scoped RatFunc
attribute [local instance] Polynomial.algebra Ideal.Quotient.field

noncomputable section

universe u

variable {k : Type u} [Field k]

example (a : k) (p : k[X]) [Fact (Irreducible p)] (hp : p.Monic)
    (x : RatFunc (AdjoinRoot p)) :
    (AdjoinRoot.rationalCoefficientAlgEquiv p hp).symm
        (RatFunc.laurent (algebraMap k (AdjoinRoot p) a) x) =
      AdjoinRoot.map (RatFunc.laurent a).toRingHom
        (p.map RatFunc.C) (p.map RatFunc.C) (by rw [RatFunc.map_C_laurent a])
        ((AdjoinRoot.rationalCoefficientAlgEquiv p hp).symm x) :=
  AdjoinRoot.rationalCoefficientAlgEquiv_symm_laurent a p hp x

variable [CharZero k] {d : ℕ} (p : MonicIrreducibleOfDegree k d) (a : k)

local instance testRationalTranslation_factIrreducible : Fact (Irreducible (poly p)) :=
  ⟨irreducible p⟩

local instance testRationalTranslation_finiteRoot : Module.Finite k (AdjoinRoot (poly p)) :=
  (AdjoinRoot.powerBasis (ne_zero p)).finite

local instance testRationalTranslation_finiteRatFuncRoot :
    Module.Finite (RatFunc k) (RatFunc (AdjoinRoot (poly p))) :=
  FiniteDimensional.of_finrank_pos (by
    rw [AdjoinRoot.finrank_ratFunc_adjoinRoot]
    exact (irreducible p).natDegree_pos)

variable [Normal k (AdjoinRoot (poly p))]

example (hp : d.Prime) (x : MilnorKRing (RatFunc (AdjoinRoot (poly p)))) :
    milnorKNormRing (RatFunc k) (RatFunc (AdjoinRoot (poly p)))
        (milnorKRingMap (RatFunc.laurent (algebraMap k (AdjoinRoot (poly p)) a)).toRingHom x) =
      milnorKRingMap (RatFunc.laurent a).toRingHom
        (milnorKNormRing (RatFunc k) (RatFunc (AdjoinRoot (poly p))) x) :=
  milnorKNormRing_ratFunc_map_laurent p a hp x

example (hp : d.Prime) (n : ℕ)
    (x : MilnorKTheory (RatFunc (AdjoinRoot (poly p))) n) :
    milnorKNorm (RatFunc k) (RatFunc (AdjoinRoot (poly p))) n
        (milnorKTheoryMap
          (RatFunc.laurent (algebraMap k (AdjoinRoot (poly p)) a)).toRingHom n x) =
      milnorKTheoryMap (RatFunc.laurent a).toRingHom n
        (milnorKNorm (RatFunc k) (RatFunc (AdjoinRoot (poly p))) n x) :=
  milnorKNorm_ratFunc_map_laurent p a hp n x
