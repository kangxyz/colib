module

import Colib.RingTheory.KTheory.MilnorK.Norm.SeparableScalarFactors

noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree
attribute [local instance] Ideal.Quotient.field

universe u v

local instance consumer_nativeIrreducible {F : Type*} [Field F]
    {d : ℕ} (r : MonicIrreducibleOfDegree F d) : Fact (Irreducible (poly r)) :=
  ⟨irreducible r⟩

/-- The finiteness construction allows independent coefficient-field universes. -/
example {k : Type u} [Field k] {K : Type v} [Field K]
    (φ : k →+* K) (p : k[X]) (hp : p ≠ 0) :
    Fintype {r : Σ d : ℕ, MonicIrreducibleOfDegree K d // poly r.2 ∣ p.map φ} :=
  coefficientFactorFintype φ p hp

/-- Repeated factors are excluded by proved separability, not by an index assumption. -/
example {k : Type u} [Field k] {K : Type v} [Field K]
    (φ : k →+* K) {d e : ℕ} (p : MonicIrreducibleOfDegree k d)
    (q : MonicIrreducibleOfDegree K e) (hp : (poly p).Separable)
    (hq : poly q ∣ (poly p).map φ) :
    multiplicity (poly q) ((poly p).map φ) = 1 :=
  multiplicity_eq_one_of_separable_map φ p q hp hq

variable {k K : Type u} [Field k] [Field K]
  (φ : k →+* K) {d : ℕ} (p : MonicIrreducibleOfDegree k d)

example (hp : (poly p).Separable)
    [Fintype {r : Σ e : ℕ, MonicIrreducibleOfDegree K e //
      poly r.2 ∣ (poly p).map φ}]
    (x : MilnorKRing (AdjoinRoot (poly p))) :
    milnorKRingMap φ (simpleMilnorNorm p x) =
      ∑ r : {r : Σ e : ℕ, MonicIrreducibleOfDegree K e //
          poly r.2 ∣ (poly p).map φ},
        simpleMilnorNorm r.1.2
          (milnorKRingMap (AdjoinRoot.map φ (poly p) (poly r.1.2) r.2) x) :=
  simpleMilnorNorm_map_eq_sum_scalarFactors_of_separable φ p hp x

example [CharZero k]
    [Fintype {r : Σ e : ℕ, MonicIrreducibleOfDegree K e //
      poly r.2 ∣ (poly p).map φ}]
    (n : ℕ) (x : MilnorKTheory (AdjoinRoot (poly p)) n) :
    milnorKRingMap φ (simpleMilnorNorm p (x : MilnorKRing (AdjoinRoot (poly p)))) =
      ∑ r : {r : Σ e : ℕ, MonicIrreducibleOfDegree K e //
          poly r.2 ∣ (poly p).map φ},
        simpleMilnorNorm r.1.2
          (milnorKRingMap (AdjoinRoot.map φ (poly p) (poly r.1.2) r.2)
            (x : MilnorKRing (AdjoinRoot (poly p)))) :=
  simpleMilnorNorm_map_eq_sum_scalarFactors φ p (x : MilnorKRing (AdjoinRoot (poly p)))

end
