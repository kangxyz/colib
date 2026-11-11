/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Norm.PrimeInseparablePresentation

noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree
attribute [local instance] Ideal.Quotient.field

universe u

variable {k : Type u} [Field k]

/-- The actual positive-degree formula in a purely inseparable root field. -/
example {ell : ℕ} (p q : MonicIrreducibleOfDegree k ell) (hprime : ell.Prime)
    [IsPurelyInseparable k (k[X] ⧸ Ideal.span {poly p})]
    (f : (k[X] ⧸ Ideal.span {poly p}) ≃ₐ[k] (k[X] ⧸ Ideal.span {poly q}))
    (m : ℕ) (x : MilnorKTheory (k[X] ⧸ Ideal.span {poly p}) (m + 1)) :
    simpleMilnorNorm p (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})) =
      simpleMilnorNorm q (milnorKRingMap f.toRingHom
        (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p}))) :=
  simpleMilnorNorm_eq_map_algEquiv_of_prime_homogeneous_of_isPurelyInseparable
    p q hprime f m x

/-- The extension degree may be the characteristic without a separability instance. -/
example {ell : ℕ} [CharP k ell]
    (p q : MonicIrreducibleOfDegree k ell) (hprime : ell.Prime)
    [IsPurelyInseparable k (k[X] ⧸ Ideal.span {poly p})]
    (f : (k[X] ⧸ Ideal.span {poly p}) ≃ₐ[k] (k[X] ⧸ Ideal.span {poly q}))
    (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})) :
    simpleMilnorNorm p x = simpleMilnorNorm q (milnorKRingMap f.toRingHom x) :=
  simpleMilnorNorm_eq_map_algEquiv_of_prime_of_isPurelyInseparable p q hprime f x

/-- The result identifies the original additive maps, not a new chosen norm. -/
example {ell : ℕ} (p q : MonicIrreducibleOfDegree k ell) (hprime : ell.Prime)
    [IsPurelyInseparable k (k[X] ⧸ Ideal.span {poly p})]
    (f : (k[X] ⧸ Ideal.span {poly p}) ≃ₐ[k] (k[X] ⧸ Ideal.span {poly q})) :
    simpleMilnorNorm p =
      (simpleMilnorNorm q).comp (milnorKRingMap f.toRingHom).toAddMonoidHom :=
  simpleMilnorNorm_eq_comp_of_prime_of_isPurelyInseparable p q hprime f

end
