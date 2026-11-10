/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Norm.RationalFiniteResidueSeparable

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree
open scoped RatFunc
attribute [local instance] Polynomial.algebra Ideal.Quotient.field
  rationalInert_nativeMonic rationalInert_nativeIrreducible rationalInert_rootFinite
  rationalInert_rationalFinite

noncomputable section

universe u

variable {k : Type u} [Field k] {d e : ℕ}
  (p : MonicIrreducibleOfDegree k d) (hsep : (poly p).Separable) (hp : d.Prime)
  [Normal k (AdjoinRoot (poly p))] (h : MonicIrreducibleOfDegree k e)

include hsep hp

local notation "E" => AdjoinRoot (poly p)
local notation "H" => AdjoinRoot (poly h)

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
          (milnorKRingMap
            ((AdjoinRoot.tensorSwapFactorQuotientEquiv (poly p) (poly h) q).toRingHom :
              (E[X] ⧸ Ideal.span {poly q.1.2}) →+*
                (H[X] ⧸ Ideal.span {poly r.1.2}))
            (monicIrreducibleResidue i.1.2 (x : MilnorKRing (RatFunc E)))) :=
  monicIrreducibleResidue_milnorKNorm_ratFunc_eq_sum_tensorSwap_of_separable
    p hsep hp h S hS n x

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
              (milnorKRingMap
                ((AdjoinRoot.tensorSwapFactorQuotientEquiv
                  (poly p) (poly h) q).toRingHom :
                    (E[X] ⧸ Ideal.span {poly q.1.2}) →+*
                      (H[X] ⧸ Ideal.span {poly r.1.2}))
                (monicIrreducibleResidue i.1.2 (x : MilnorKRing (RatFunc E)))) :=
  exists_finset_monicIrreducibleResidue_milnorKNorm_ratFunc_eq_sum_tensorSwap_of_separable
    p hsep hp h
