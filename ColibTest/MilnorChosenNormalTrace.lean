/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Norm.ChosenNormalTrace

/-!
Consumers of the characteristic-zero chosen-norm trace in arbitrary finite normal
extensions. No presentation, prime degree or separate separability premise is supplied.
-/

noncomputable section

open Stacks.Chow
open scoped BigOperators

universe u

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  [FiniteDimensional k L] [Normal k L] [CharZero k]

example (x : MilnorKRing L) :
    milnorKRingMap (algebraMap k L) (milnorKNormRing k L x) =
      ∑ σ : L →ₐ[k] L, milnorKRingMap σ.toRingHom x :=
  milnorKNormRing_map_eq_sum_algHom_of_normal x

example (x : MilnorKRing L) :
    milnorKRingMap (algebraMap k L) (milnorKNormRing k L x) =
      ∑ σ : Gal(L/k), milnorKRingMap σ.toRingHom x :=
  milnorKNormRing_map_eq_sum_gal_of_normal x

example (n : ℕ) (x : MilnorKTheory L n) :
    milnorKTransport (algebraMap k L) n (milnorKNorm k L n x) =
      ∑ σ : Gal(L/k), milnorKTransport σ.toRingHom n x :=
  milnorKNorm_map_eq_sum_gal_of_normal n x

example (x : MilnorKRing L)
    (hx : ∀ σ : Gal(L/k), milnorKRingMap σ.toRingHom x = x) :
    milnorKRingMap (algebraMap k L) (milnorKNormRing k L x) =
      Fintype.card Gal(L/k) • x := by
  classical
  rw [milnorKNormRing_map_eq_sum_gal_of_normal x]
  simp only [hx, Finset.sum_const, Finset.card_univ]

example (x : MilnorKTheory L 0) :
    milnorKTransport (algebraMap k L) 0 (milnorKNorm k L 0 x) =
      ∑ σ : Gal(L/k), milnorKTransport σ.toRingHom 0 x :=
  milnorKNorm_map_eq_sum_gal_of_normal 0 x

example (n : ℕ) (x : MilnorKTheory k n) :
    milnorKTransport (algebraMap k k) n (milnorKNorm k k n x) =
      ∑ σ : Gal(k/k), milnorKTransport σ.toRingHom n x :=
  milnorKNorm_map_eq_sum_gal_of_normal n x

end
