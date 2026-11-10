module

import Colib.RingTheory.KTheory.MilnorK.Norm.RationalFiniteResidue

noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree
open scoped RatFunc
attribute [local instance] Polynomial.algebra Ideal.Quotient.field

universe u

local instance testRationalFiniteResidue_linearMaximal {F : Type u} [Field F] (a : F) :
    (Ideal.span ({X - C a} : Set F[X])).IsMaximal :=
  isMaximal_span_singleton_of_irreducible_polynomial (irreducible_X_sub_C a)

local instance testRationalFiniteResidue_nativeIrreducible {F : Type u} [Field F]
    {d : ℕ} (p : MonicIrreducibleOfDegree F d) : Fact (Irreducible (poly p)) :=
  ⟨irreducible p⟩

local instance testRationalFiniteResidue_rootFinite {F : Type u} [Field F]
    {d : ℕ} (p : MonicIrreducibleOfDegree F d) : Module.Finite F (AdjoinRoot (poly p)) :=
  (AdjoinRoot.powerBasis (ne_zero p)).finite

local instance testRationalFiniteResidue_rationalFinite {F : Type u} [Field F]
    {d : ℕ} (p : MonicIrreducibleOfDegree F d) :
    Module.Finite (RatFunc F) (RatFunc (AdjoinRoot (poly p))) :=
  FiniteDimensional.of_finrank_pos (by
    rw [AdjoinRoot.finrank_ratFunc_adjoinRoot]
    exact (irreducible p).natDegree_pos)

variable {k K : Type u} [Field k] [Field K] {d e : ℕ}

example
    (φ : k →+* K) (p : MonicIrreducibleOfDegree k d) (hs : (poly p).Separable)
    (q : MonicIrreducibleOfDegree K e) (hq : poly q ∣ (poly p).map φ) :
    multiplicity (poly q) ((poly p).map φ) = 1 :=
  multiplicity_eq_one_of_nativeFactor_dvd_map_of_separable φ p hs q hq

example [CharZero k] (φ : k →+* K) (p : MonicIrreducibleOfDegree k d)
    (q : MonicIrreducibleOfDegree K e) (hq : poly q ∣ (poly p).map φ) :
    multiplicity (poly q) ((poly p).map φ) = 1 :=
  multiplicity_eq_one_of_nativeFactor_dvd_map_of_separable φ p
    (irreducible p).separable q hq

example
    [CharZero k] (φ : k →+* K) (p : MonicIrreducibleOfDegree k d) (hp : d.Prime)
    [Normal k (AdjoinRoot (poly p))]
    (q : MonicIrreducibleOfDegree K e) (hq : poly q ∣ (poly p).map φ)
    (a : K) (n : ℕ) (x : MilnorKTheory (RatFunc (AdjoinRoot (poly q))) (n + 1)) :
    milnorKRingMap (quotientSpanXSubCAlgEquiv a).toRingHom
        (monicIrreducibleResidue
          (⟨X - C a, monic_X_sub_C a, irreducible_X_sub_C a, natDegree_X_sub_C a⟩ :
            MonicIrreducibleOfDegree K 1)
          (milnorKNorm (RatFunc K) (RatFunc (AdjoinRoot (poly q)))
            (n + 1) x : MilnorKRing (RatFunc K))) =
      simpleMilnorNorm q
        (milnorKRingMap
          (quotientSpanXSubCAlgEquiv (algebraMap K (AdjoinRoot (poly q)) a)).toRingHom
          (monicIrreducibleResidue
            (⟨X - C (algebraMap K (AdjoinRoot (poly q)) a),
              monic_X_sub_C _, irreducible_X_sub_C _, natDegree_X_sub_C _⟩ :
                MonicIrreducibleOfDegree (AdjoinRoot (poly q)) 1)
            (x : MilnorKRing (RatFunc (AdjoinRoot (poly q)))))) :=
  monicIrreducibleResidue_X_sub_C_milnorKNorm_ratFunc_of_scalarFactor φ p hp q hq a n x

variable [CharZero k] (p : MonicIrreducibleOfDegree k d) (hp : d.Prime)
  [Normal k (AdjoinRoot (poly p))] (h : MonicIrreducibleOfDegree k e)

local notation "E" => AdjoinRoot (poly p)
local notation "H" => AdjoinRoot (poly h)

example
    (S : Finset (Σ f : ℕ, MonicIrreducibleOfDegree E f))
    (hS : ∀ q, q ∈ S ↔ poly q.2 ∣ (poly h).map (algebraMap k E))
    (T : Finset (Σ f : ℕ, MonicIrreducibleOfDegree H f))
    (hT : ∀ r, r ∈ T ↔ poly r.2 ∣ (poly p).map (algebraMap k H)) :
    Nonempty (S ≃ T) :=
  ⟨(Equiv.subtypeEquivRight hS).trans
    ((AdjoinRoot.tensorSwapFactorIndexEquiv (poly p) (poly h)).trans
      (Equiv.subtypeEquivRight hT).symm)⟩

example
    (S : Finset (Σ f : ℕ, MonicIrreducibleOfDegree E f))
    (hS : ∀ q, q ∈ S ↔ poly q.2 ∣ (poly h).map (algebraMap k E))
    (n : ℕ) (x : MilnorKTheory (RatFunc E) (n + 1)) :
    monicIrreducibleResidue h
        (milnorKNorm (RatFunc k) (RatFunc E) (n + 1) x : MilnorKRing (RatFunc k)) =
      ∑ i ∈ S.attach,
        let q : {q : Σ f : ℕ, MonicIrreducibleOfDegree E f //
            poly q.2 ∣ (poly h).map (algebraMap k E)} := ⟨i.1, (hS i.1).mp i.2⟩
        let r := AdjoinRoot.tensorSwapFactorIndexEquiv (poly p) (poly h) q
        simpleMilnorNorm r.1.2
          (@milnorKRingMap
            (E[X] ⧸ Ideal.span {poly q.1.2}) (H[X] ⧸ Ideal.span {poly r.1.2})
            (Ideal.Quotient.field _) (Ideal.Quotient.field _)
            ((AdjoinRoot.tensorSwapFactorQuotientEquiv (poly p) (poly h) q).toRingHom :
              (E[X] ⧸ Ideal.span {poly q.1.2}) →+*
                (H[X] ⧸ Ideal.span {poly r.1.2}))
            (monicIrreducibleResidue q.1.2 (x : MilnorKRing (RatFunc E)))) :=
  monicIrreducibleResidue_milnorKNorm_ratFunc_eq_sum_tensorSwap p hp h S hS n x

example :
    ∃ (S : Finset (Σ f : ℕ, MonicIrreducibleOfDegree E f))
      (hS : ∀ q, q ∈ S ↔ poly q.2 ∣ (poly h).map (algebraMap k E)),
      ∀ (n : ℕ) (x : MilnorKTheory (RatFunc E) (n + 1)),
        monicIrreducibleResidue h
            (milnorKNorm (RatFunc k) (RatFunc E) (n + 1) x :
              MilnorKRing (RatFunc k)) =
          ∑ i ∈ S.attach,
            let q : {q : Σ f : ℕ, MonicIrreducibleOfDegree E f //
                poly q.2 ∣ (poly h).map (algebraMap k E)} := ⟨i.1, (hS i.1).mp i.2⟩
            let r := AdjoinRoot.tensorSwapFactorIndexEquiv (poly p) (poly h) q
            simpleMilnorNorm r.1.2
              (@milnorKRingMap
                (E[X] ⧸ Ideal.span {poly q.1.2}) (H[X] ⧸ Ideal.span {poly r.1.2})
                (Ideal.Quotient.field _) (Ideal.Quotient.field _)
                ((AdjoinRoot.tensorSwapFactorQuotientEquiv
                  (poly p) (poly h) q).toRingHom :
                    (E[X] ⧸ Ideal.span {poly q.1.2}) →+*
                      (H[X] ⧸ Ideal.span {poly r.1.2}))
                (monicIrreducibleResidue q.1.2 (x : MilnorKRing (RatFunc E)))) :=
  exists_finset_monicIrreducibleResidue_milnorKNorm_ratFunc_eq_sum_tensorSwap p hp h
