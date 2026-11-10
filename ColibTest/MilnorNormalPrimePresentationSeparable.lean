module

import Colib.RingTheory.KTheory.MilnorK.Norm.NormalPrimePresentationSeparable

noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree
attribute [local instance] Ideal.Quotient.field

universe u

variable {k : Type u} [Field k]

/-- The coprime annihilator does not use normality, separability or perfectness. -/
example {ell : ℕ} (p q : MonicIrreducibleOfDegree k ell) (hprime : ell.Prime)
    (f : (k[X] ⧸ Ideal.span {poly p}) ≃ₐ[k] (k[X] ⧸ Ideal.span {poly q}))
    (m : ℕ) (x : MilnorKTheory (k[X] ⧸ Ideal.span {poly p}) (m + 1)) :
    ∃ d : ℕ, ell.Coprime d ∧
      (d : ℤ) • (simpleMilnorNorm p (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})) -
        simpleMilnorNorm q (milnorKRingMap f.toRingHom
          (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})))) = 0 :=
  simpleMilnorNorm_difference_exists_coprime_smul_arbitrary p q hprime f m x

/-- The prime extension degree may equal the base characteristic. Only the
actual root extension is separable; no perfectness instance is available. -/
example {ell : ℕ} [CharP k ell]
    (p q : MonicIrreducibleOfDegree k ell) (hprime : ell.Prime)
    [Algebra.IsSeparable k (k[X] ⧸ Ideal.span {poly p})]
    [Normal k (k[X] ⧸ Ideal.span {poly p})]
    (f : (k[X] ⧸ Ideal.span {poly p}) ≃ₐ[k] (k[X] ⧸ Ideal.span {poly q}))
    (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})) :
    simpleMilnorNorm p x = simpleMilnorNorm q (milnorKRingMap f.toRingHom x) :=
  simpleMilnorNorm_eq_map_algEquiv_of_normal_prime_of_separable p q hprime f x

/-- Equality concerns the original additive norm maps and actual equivalence. -/
example {ell : ℕ} (p q : MonicIrreducibleOfDegree k ell) (hprime : ell.Prime)
    [Algebra.IsSeparable k (k[X] ⧸ Ideal.span {poly p})]
    [Normal k (k[X] ⧸ Ideal.span {poly p})]
    (f : (k[X] ⧸ Ideal.span {poly p}) ≃ₐ[k] (k[X] ⧸ Ideal.span {poly q})) :
    simpleMilnorNorm p =
      (simpleMilnorNorm q).comp (milnorKRingMap f.toRingHom).toAddMonoidHom :=
  simpleMilnorNorm_eq_comp_of_normal_prime_of_separable p q hprime f

end
