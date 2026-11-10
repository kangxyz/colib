module

import Colib.RingTheory.KTheory.MilnorK.Norm.RationalDegreeOne

noncomputable section

open Polynomial
open scoped RatFunc
attribute [local instance] Polynomial.algebra

universe u

local instance testRationalDegreeOne_isMaximal_span_X_sub_C
    {K : Type u} [Field K] (b : K) :
    (Ideal.span ({X - C b} : Set K[X])).IsMaximal :=
  Stacks.Chow.isMaximal_span_singleton_of_irreducible_polynomial (irreducible_X_sub_C b)

open Stacks.Chow MonicIrreducibleOfDegree

attribute [local instance] Ideal.Quotient.field

variable {k K : Type u} [Field k] [Field K]

example (φ : k →+* K) (a : k) (h : X - C (φ a) ∣ (X - C a).map φ) :
    (quotientSpanXSubCAlgEquiv (φ a)).toRingHom.comp
        (AdjoinRoot.map φ (X - C a) (X - C (φ a)) h) =
      φ.comp (quotientSpanXSubCAlgEquiv a).toRingHom :=
  quotientSpanXSubCAlgEquiv_comp_adjoinRoot_map φ a h

example
    (φ : k →+* K) (a : k) (x : MilnorKRing (RatFunc k)) :
    milnorKRingMap (quotientSpanXSubCAlgEquiv (φ a)).toRingHom
        (monicIrreducibleResidue
          (⟨X - C (φ a), monic_X_sub_C _, irreducible_X_sub_C _, natDegree_X_sub_C _⟩ :
            MonicIrreducibleOfDegree K 1)
          (milnorKRingMap
            (RatFunc.mapRingHom (Polynomial.mapRingHom φ)
              (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)) x)) =
      milnorKRingMap φ
        (milnorKRingMap (quotientSpanXSubCAlgEquiv a).toRingHom
          (monicIrreducibleResidue
            (⟨X - C a, monic_X_sub_C a, irreducible_X_sub_C a, natDegree_X_sub_C a⟩ :
              MonicIrreducibleOfDegree k 1) x)) :=
  monicIrreducibleResidue_X_sub_C_mapRingHom φ a x

variable (p : MonicIrreducibleOfDegree k 1)

local instance testRationalDegreeOne_factIrreducible : Fact (Irreducible (poly p)) :=
  ⟨irreducible p⟩

local instance testRationalDegreeOne_finiteRoot : Module.Finite k (AdjoinRoot (poly p)) :=
  (AdjoinRoot.powerBasis (ne_zero p)).finite

local instance testRationalDegreeOne_finiteRatFuncRoot :
    Module.Finite (RatFunc k) (RatFunc (AdjoinRoot (poly p))) :=
  FiniteDimensional.of_finrank_pos (by
    rw [AdjoinRoot.finrank_ratFunc_adjoinRoot]
    exact (irreducible p).natDegree_pos)

example : Function.Bijective
    (algebraMap (RatFunc k) (RatFunc (AdjoinRoot (poly p)))) :=
  algebraMap_ratFunc_adjoinRoot_bijective_of_degree_one p

example
    (a : k) (x : MilnorKRing (RatFunc (AdjoinRoot (poly p)))) :
    milnorKRingMap (quotientSpanXSubCAlgEquiv a).toRingHom
        (monicIrreducibleResidue
          (⟨X - C a, monic_X_sub_C a, irreducible_X_sub_C a, natDegree_X_sub_C a⟩ :
            MonicIrreducibleOfDegree k 1)
          (milnorKNormRing (RatFunc k) (RatFunc (AdjoinRoot (poly p))) x)) =
      milnorKNormRing k (AdjoinRoot (poly p))
        (milnorKRingMap
          (quotientSpanXSubCAlgEquiv (algebraMap k (AdjoinRoot (poly p)) a)).toRingHom
          (monicIrreducibleResidue
            (⟨X - C (algebraMap k (AdjoinRoot (poly p)) a),
              monic_X_sub_C _, irreducible_X_sub_C _, natDegree_X_sub_C _⟩ :
                MonicIrreducibleOfDegree (AdjoinRoot (poly p)) 1) x)) :=
  monicIrreducibleResidue_X_sub_C_milnorKNormRing_ratFunc_of_degree_one p a x

example
    (a : k) (n : ℕ) (x : MilnorKTheory (RatFunc (AdjoinRoot (poly p))) (n + 1)) :
    milnorKRingMap (quotientSpanXSubCAlgEquiv a).toRingHom
        (monicIrreducibleResidue
          (⟨X - C a, monic_X_sub_C a, irreducible_X_sub_C a, natDegree_X_sub_C a⟩ :
            MonicIrreducibleOfDegree k 1)
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
  monicIrreducibleResidue_X_sub_C_milnorKNorm_ratFunc_of_degree_one p a n x
