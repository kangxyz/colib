/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Norm.NormalPrimeScalarBaseChange
import Colib.RingTheory.KTheory.MilnorK.Norm.NormalPrimeScalarBaseChangeSeparable

/-! Typed consumers over arbitrary coefficient fields, without perfectness or characteristic zero.
-/

noncomputable section

open Polynomial Module Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree

universe u v

attribute [local instance] Ideal.Quotient.field

variable {k K : Type u} [Field k] [Field K]

example
    {d : ℕ} (p : MonicIrreducibleOfDegree k d) (hsep : (poly p).Separable) :
    Algebra.IsSeparable k (k[X] ⧸ Ideal.span {poly p}) :=
  isSeparable_quotient_of_polynomial_separable p hsep

example
    {L : Type u} [Field L] [Algebra k L]
    [FiniteDimensional k L] [Algebra.IsSeparable k L] [Normal k L]
    {d : ℕ} (p : MonicIrreducibleOfDegree k d) (hd : d = 1 ∨ d.Prime)
    (f : L ≃ₐ[k] (k[X] ⧸ Ideal.span {poly p})) (x : MilnorKRing L) :
    milnorKNormRing k L x = simpleMilnorNorm p (milnorKRingMap f.toRingHom x) :=
  milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_one_or_normal_prime_of_separable p hd f x

example
    {d : ℕ} (p : MonicIrreducibleOfDegree k d)
    (hd : d = 1 ∨ d.Prime)
    [FiniteDimensional k (k[X] ⧸ Ideal.span {poly p})]
    [Algebra.IsSeparable k (k[X] ⧸ Ideal.span {poly p})]
    [Normal k (k[X] ⧸ Ideal.span {poly p})]
    (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})) :
    milnorKNormRing k (k[X] ⧸ Ideal.span {poly p}) x = simpleMilnorNorm p x :=
  milnorKNormRing_eq_simpleMilnorNorm_of_one_or_normal_prime_of_separable p hd x

example
    (φ : k →+* K) {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (hsep : (poly p).Separable) (hp : d.Prime)
    [Normal k (k[X] ⧸ Ideal.span {poly p})]
    (q : MonicIrreducibleOfDegree K e) (hq : poly q ∣ (poly p).map φ) :
    e = 1 ∨ e = d :=
  degree_eq_one_or_eq_of_dvd_map_of_normal_prime_of_separable φ p hsep hp q hq

example
    (φ : k →+* K) {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (hsep : (poly p).Separable) (hp : d.Prime)
    [Normal k (k[X] ⧸ Ideal.span {poly p})]
    (q : MonicIrreducibleOfDegree K e) (hq : poly q ∣ (poly p).map φ)
    [FiniteDimensional K (K[X] ⧸ Ideal.span {poly q})]
    (x : MilnorKRing (K[X] ⧸ Ideal.span {poly q})) :
    milnorKNormRing K (K[X] ⧸ Ideal.span {poly q}) x = simpleMilnorNorm q x :=
  milnorKNormRing_eq_simpleMilnorNorm_of_dvd_map_of_normal_prime_of_separable φ p hsep hp q hq x

example
    (φ : k →+* K) {d : ℕ} (p : MonicIrreducibleOfDegree k d)
    (hsep : (poly p).Separable) (hp : d.Prime)
    [Normal k (k[X] ⧸ Ideal.span {poly p})]
    [Fintype {r : Σ e : ℕ, MonicIrreducibleOfDegree K e //
      poly r.2 ∣ (poly p).map φ}]
    (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})) :
    let : FiniteDimensional k (k[X] ⧸ Ideal.span {poly p}) :=
      (AdjoinRoot.powerBasis' (monic p)).finite
    let : ∀ r : {r : Σ e : ℕ, MonicIrreducibleOfDegree K e //
        poly r.2 ∣ (poly p).map φ},
        FiniteDimensional K (K[X] ⧸ Ideal.span {poly r.1.2}) :=
      fun r => (AdjoinRoot.powerBasis' (monic r.1.2)).finite
    milnorKRingMap φ (milnorKNormRing k (k[X] ⧸ Ideal.span {poly p}) x) =
      ∑ r : {r : Σ e : ℕ, MonicIrreducibleOfDegree K e //
          poly r.2 ∣ (poly p).map φ},
        milnorKNormRing K (K[X] ⧸ Ideal.span {poly r.1.2})
          (milnorKRingMap (AdjoinRoot.map φ (poly p) (poly r.1.2) r.2) x) :=
  milnorKNormRing_map_eq_sum_scalarFactors_of_normal_prime_of_separable φ p hsep hp x

example
    {ι : Type v} (φ : k →+* K)
    {L : Type u} [Field L] [Algebra k L] [FiniteDimensional k L] [Normal k L]
    {d : ℕ} (p : MonicIrreducibleOfDegree k d) (hsep : (poly p).Separable) (hp : d.Prime)
    (f : L ≃ₐ[k] (k[X] ⧸ Ideal.span {poly p}))
    (S : Finset ι) (e : ι → ℕ) (q : ∀ i, MonicIrreducibleOfDegree K (e i))
    (hinj : Set.InjOn (fun i => poly (q i)) (S : Set ι))
    (hq : ∀ i, poly (q i) ∣ (poly p).map φ)
    (hcover : ∀ (a : ℕ) (r : MonicIrreducibleOfDegree K a),
      poly r ∣ (poly p).map φ → ∃ i ∈ S, poly r = poly (q i))
    (M : ι → Type u) [∀ i, Field (M i)] [∀ i, Algebra K (M i)]
    [∀ i, FiniteDimensional K (M i)]
    (g : ∀ i, M i ≃ₐ[K] (K[X] ⧸ Ideal.span {poly (q i)}))
    (j : ∀ i, L →+* M i)
    (hsquare : ∀ i, (g i).toRingHom.comp (j i) =
      (AdjoinRoot.map φ (poly p) (poly (q i)) (hq i)).comp f.toRingHom)
    (x : MilnorKRing L) :
    milnorKRingMap φ (milnorKNormRing k L x) =
      ∑ i ∈ S, milnorKNormRing K (M i) (milnorKRingMap (j i) x) :=
  milnorKNormRing_map_eq_sum_of_branch_equivs_of_normal_prime_of_separable
    φ p hsep hp f S e q hinj hq hcover M g j hsquare x

end
