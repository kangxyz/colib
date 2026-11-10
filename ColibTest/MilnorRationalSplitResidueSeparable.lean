/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Norm.RationalSplitResidueSeparable

noncomputable section

open Polynomial Stacks.Chow MonicIrreducibleOfDegree
open scoped RatFunc
attribute [local instance] Polynomial.algebra

universe u

attribute [local instance] Ideal.Quotient.field

variable {k : Type u} [Field k] {d e : ℕ}
  (p : MonicIrreducibleOfDegree k d) (h : MonicIrreducibleOfDegree k e)

local instance : Fact (Irreducible (poly p)) := ⟨irreducible p⟩
local instance : Fact (Irreducible (poly h)) := ⟨irreducible h⟩
local instance : Module.Finite k (AdjoinRoot (poly p)) :=
  (AdjoinRoot.powerBasis (ne_zero p)).finite
local instance : Module.Finite (RatFunc k) (RatFunc (AdjoinRoot (poly p))) :=
  FiniteDimensional.of_finrank_pos (by
    rw [AdjoinRoot.finrank_ratFunc_adjoinRoot]
    exact (irreducible p).natDegree_pos)

local notation "E" => AdjoinRoot (poly p)
local notation "H" => AdjoinRoot (poly h)

-- The original chosen norm and the full actual tensor-swap sum, explicitly
-- allowing an inseparable closed point and every homogeneous Milnor degree.
example (hsep : (poly p).Separable) (hp : d.Prime) [Normal k E]
    (_hnotsep : ¬(poly h).Separable) (f : AdjoinRoot (poly p) →ₐ[k] AdjoinRoot (poly h))
    (S : Finset (Σ a : ℕ, MonicIrreducibleOfDegree E a))
    (hS : ∀ q, q ∈ S ↔ poly q.2 ∣ (poly h).map (algebraMap k E))
    (n : ℕ) (x : MilnorKTheory (RatFunc E) (n + 1)) :
    monicIrreducibleResidue h
        (milnorKNorm (RatFunc k) (RatFunc E) (n + 1) x : MilnorKRing (RatFunc k)) =
      ∑ i ∈ S.attach,
        let q : {q : Σ a : ℕ, MonicIrreducibleOfDegree E a //
            poly q.2 ∣ (poly h).map (algebraMap k E)} := ⟨i.1, (hS i.1).mp i.2⟩
        let r := AdjoinRoot.tensorSwapFactorIndexEquiv (poly p) (poly h) q
        simpleMilnorNorm r.1.2
          (@milnorKRingMap
            (E[X] ⧸ Ideal.span {poly q.1.2}) (H[X] ⧸ Ideal.span {poly r.1.2})
            (Ideal.Quotient.field _) (Ideal.Quotient.field _)
            (AdjoinRoot.tensorSwapFactorQuotientEquiv (poly p) (poly h) q).toRingHom
            (monicIrreducibleResidue q.1.2 (x : MilnorKRing (RatFunc E)))) :=
  monicIrreducibleResidue_milnorKNormRing_ratFunc_eq_sum_tensorSwap_of_split
    p hsep hp h f S hS (x : MilnorKRing (RatFunc E))
