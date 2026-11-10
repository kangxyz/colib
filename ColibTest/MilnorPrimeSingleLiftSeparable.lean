/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Norm.PrimeSingleLiftSeparable

noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree
open scoped RatFunc
attribute [local instance] Polynomial.algebra Ideal.Quotient.field

universe u

local instance consumer_nativeIrreducible {F : Type u} [Field F]
    {d : ℕ} (p : MonicIrreducibleOfDegree F d) : Fact (Irreducible (poly p)) :=
  ⟨irreducible p⟩

local instance consumer_rootFinite {F : Type u} [Field F]
    {d : ℕ} (p : MonicIrreducibleOfDegree F d) : Module.Finite F (AdjoinRoot (poly p)) :=
  (AdjoinRoot.powerBasis (ne_zero p)).finite

local instance consumer_rationalFinite {F : Type u} [Field F]
    {d : ℕ} (p : MonicIrreducibleOfDegree F d) :
    Module.Finite (RatFunc F) (RatFunc (AdjoinRoot (poly p))) :=
  FiniteDimensional.of_finrank_pos (by
    rw [AdjoinRoot.finrank_ratFunc_adjoinRoot]
    exact (irreducible p).natDegree_pos)

variable {k : Type u} [Field k] {d e : ℕ}
  (p : MonicIrreducibleOfDegree k d) (hsep : (poly p).Separable) (hp : d.Prime)
  [Normal k (AdjoinRoot (poly p))] (h : MonicIrreducibleOfDegree k e)
  (q : {q : Σ f : ℕ, MonicIrreducibleOfDegree (AdjoinRoot (poly p)) f //
    poly q.2 ∣ (poly h).map (algebraMap k (AdjoinRoot (poly p)))})

/-- The lift is supplied by the native surjectivity theorem, not as a hypothesis. -/
example (n : ℕ) (z : MilnorKTheory (AdjoinRoot (poly q.1.2)) n) :
    ∃ x : MilnorKTheory (RatFunc (AdjoinRoot (poly p))) (n + 1),
      IsSingleResidueLift q.1.2 (z : MilnorKRing (AdjoinRoot (poly q.1.2))) (x : MilnorKRing _) ∧
      simpleMilnorNorm p (simpleMilnorNorm q.1.2 (z : MilnorKRing (AdjoinRoot (poly q.1.2)))) =
        -infinityResidueRing k
          (milnorKNorm (RatFunc k) (RatFunc (AdjoinRoot (poly p))) (n + 1) x :
            MilnorKRing (RatFunc k)) :=
  exists_isSingleResidueLift_simpleMilnorNorm_simpleMilnorNorm_of_separable p hsep hp q.1.2 n z

/-- The same actual lift calculates the norm, with its original infinity sign. -/
example (n : ℕ) (z : MilnorKRing (AdjoinRoot (poly q.1.2)))
    (x : MilnorKTheory (RatFunc (AdjoinRoot (poly p))) (n + 1))
    (hx : IsSingleResidueLift q.1.2 z (x : MilnorKRing _)) :
    simpleMilnorNorm p (simpleMilnorNorm q.1.2 z) =
      -infinityResidueRing k
        (milnorKNorm (RatFunc k) (RatFunc (AdjoinRoot (poly p))) (n + 1) x :
          MilnorKRing (RatFunc k)) :=
  simpleMilnorNorm_simpleMilnorNorm_eq_neg_infinityResidueRing_of_lift_of_separable
    p hsep hp q.1.2 z n x hx

end
