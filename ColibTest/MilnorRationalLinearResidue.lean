module

import Colib.RingTheory.KTheory.MilnorK.Norm.RationalLinearResidue

noncomputable section

open Polynomial IsLocalRing
open scoped RatFunc
attribute [local instance] Polynomial.algebra

universe u

local instance testRationalLinearResidue_isMaximal_span_X_sub_C
    {K : Type u} [Field K] (b : K) :
    (Ideal.span ({X - C b} : Set K[X])).IsMaximal :=
  Stacks.Chow.isMaximal_span_singleton_of_irreducible_polynomial (irreducible_X_sub_C b)

open Stacks.Chow

open MonicIrreducibleOfDegree

attribute [local instance] Ideal.Quotient.field

variable {k : Type u} [Field k] [CharZero k] {d : ℕ}
  (p : MonicIrreducibleOfDegree k d) (a : k)

local instance testRationalLinearResidue_factIrreducible : Fact (Irreducible (poly p)) :=
  ⟨irreducible p⟩

local instance testRationalLinearResidue_finiteRoot : Module.Finite k (AdjoinRoot (poly p)) :=
  (AdjoinRoot.powerBasis (ne_zero p)).finite

local instance testRationalLinearResidue_finiteRatFuncRoot :
    Module.Finite (RatFunc k) (RatFunc (AdjoinRoot (poly p))) :=
  FiniteDimensional.of_finrank_pos (by
    rw [AdjoinRoot.finrank_ratFunc_adjoinRoot]
    exact (irreducible p).natDegree_pos)

variable [Normal k (AdjoinRoot (poly p))]

example (hp : d.Prime) (n : ℕ)
    (x : MilnorKTheory (RatFunc (AdjoinRoot (poly p))) (n + 1)) :
    milnorKRingMap (quotientSpanXSubCAlgEquiv a).toRingHom
        (monicIrreducibleResidue
          (⟨X - C a, monic_X_sub_C a, irreducible_X_sub_C a,
            natDegree_X_sub_C a⟩ : MonicIrreducibleOfDegree k 1)
          (milnorKNorm (RatFunc k) (RatFunc (AdjoinRoot (poly p)))
            (n + 1) x : MilnorKRing (RatFunc k))) =
      milnorKNormRing k (AdjoinRoot (poly p))
        (milnorKRingMap
          (quotientSpanXSubCAlgEquiv (algebraMap k (AdjoinRoot (poly p)) a)).toRingHom
          (monicIrreducibleResidue
            (⟨X - C (algebraMap k (AdjoinRoot (poly p)) a),
              monic_X_sub_C _, irreducible_X_sub_C _, natDegree_X_sub_C _⟩ :
                MonicIrreducibleOfDegree (AdjoinRoot (poly p)) 1)
            (x : MilnorKRing (RatFunc (AdjoinRoot (poly p)))))) :=
  monicIrreducibleResidue_X_sub_C_milnorKNorm_ratFunc p a hp n x

example (hp : d.Prime)
    (x : MilnorKTheory (RatFunc (AdjoinRoot (poly p))) 1) :
    milnorKRingMap (quotientSpanXSubCAlgEquiv a).toRingHom
        (monicIrreducibleResidue
          (⟨X - C a, monic_X_sub_C a, irreducible_X_sub_C a,
            natDegree_X_sub_C a⟩ : MonicIrreducibleOfDegree k 1)
          (milnorKNorm (RatFunc k) (RatFunc (AdjoinRoot (poly p)))
            1 x : MilnorKRing (RatFunc k))) =
      milnorKNormRing k (AdjoinRoot (poly p))
        (milnorKRingMap
          (quotientSpanXSubCAlgEquiv (algebraMap k (AdjoinRoot (poly p)) a)).toRingHom
          (monicIrreducibleResidue
            (⟨X - C (algebraMap k (AdjoinRoot (poly p)) a),
              monic_X_sub_C _, irreducible_X_sub_C _, natDegree_X_sub_C _⟩ :
                MonicIrreducibleOfDegree (AdjoinRoot (poly p)) 1)
            (x : MilnorKRing (RatFunc (AdjoinRoot (poly p)))))) :=
  monicIrreducibleResidue_X_sub_C_milnorKNorm_ratFunc p a hp 0 x
